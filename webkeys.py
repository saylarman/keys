#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import re
import io
import zipfile
import json
import base64
import hashlib
from datetime import datetime, timedelta, timezone
from typing import Optional, Tuple, Dict, Any, List

from flask import Flask, render_template_string, request, send_file, send_from_directory
from werkzeug.utils import secure_filename

from cryptography import x509
from cryptography.exceptions import InvalidSignature
from cryptography.x509 import NameOID
from cryptography.hazmat.primitives import serialization, hashes
from cryptography.hazmat.primitives.serialization import Encoding, PrivateFormat, PublicFormat, NoEncryption, BestAvailableEncryption
from cryptography.hazmat.primitives.asymmetric import padding, rsa, ec, ed25519, ed448
from cryptography.hazmat.primitives.serialization.ssh import load_ssh_public_key

from jwcrypto import jwk
import plotly.graph_objs as go
import plotly.offline as pyo


# =========================
# Helpers / Utilities
# =========================

def _b64url_no_pad(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")


def hexdigest(data: bytes, algo: str) -> str:
    return getattr(hashlib, algo)(data).hexdigest()


def compute_fingerprints(raw: bytes) -> Dict[str, str]:
    return {
        "MD5": f"MD5: {hexdigest(raw, 'md5')}",
        "SHA1": f"SHA1: {hexdigest(raw, 'sha1')}",
        "SHA256": f"SHA256: {hexdigest(raw, 'sha256')}",
    }


def estimate_security(bits: int, algo: str) -> str:
    algo = algo.upper()
    if algo == "RSA":
        if bits < 2048:
            return "Weak"
        elif bits < 3072:
            return "Medium"
        else:
            return "Strong"
    if algo in ("EC", "ED25519", "OKP"):
        if bits < 224:
            return "Weak"
        elif bits < 256:
            return "Medium"
        else:
            return "Strong"
    return "Unknown"


def pem_blocks(pem_text: str, label: Optional[str] = None) -> List[str]:
    """Split concatenated PEM into list of PEM blocks. If label provided, filter to that label."""
    pattern = r"-----BEGIN ([^-]+)-----\r?\n.*?\r?\n-----END \1-----"
    blocks = [m.group(0) for m in re.finditer(pattern, pem_text, re.DOTALL)]
    if label:
        return [b for b in blocks if f"BEGIN {label}" in b]
    return blocks


def load_any_public_key(pem_or_ssh: bytes):
    """Try PEM public key → SSH public key (OpenSSH) fallback."""
    try:
        return serialization.load_pem_public_key(pem_or_ssh)
    except Exception:
        pass
    try:
        return load_ssh_public_key(pem_or_ssh)
    except Exception:
        pass
    return None


def pubkeys_equal(k1, k2) -> bool:
    """Compare two public keys by their public numbers."""
    if type(k1) is not type(k2):
        return False
    if isinstance(k1, rsa.RSAPublicKey):
        n1, e1 = k1.public_numbers().n, k1.public_numbers().e
        n2, e2 = k2.public_numbers().n, k2.public_numbers().e
        return (n1 == n2) and (e1 == e2)
    if isinstance(k1, ec.EllipticCurvePublicKey):
        n1, n2 = k1.public_numbers(), k2.public_numbers()
        return (n1.x == n2.x) and (n1.y == n2.y) and (k1.curve.name == k2.curve.name)
    if isinstance(k1, ed25519.Ed25519PublicKey):
        return k1.public_bytes(Encoding.Raw, PublicFormat.Raw) == k2.public_bytes(Encoding.Raw, PublicFormat.Raw)
    return False


def ssh_fingerprints_from_openssh_pub_line(line: str) -> Dict[str, str]:
    """
    Accepts a line like: 'ssh-rsa AAAAB3... comment'
    Returns SSH-style fingerprints (MD5 hex, SHA256 base64-no-pad).
    """
    parts = line.strip().split()
    if len(parts) < 2:
        return {}
    b64 = parts[1]
    try:
        raw = base64.b64decode(b64)
        md5_hex = ":".join([raw.hex()[i:i+2] for i in range(0, len(raw.hex()), 2)])
        sha256_b64 = base64.b64encode(hashlib.sha256(raw).digest()).decode().rstrip("=")
        return {
            "OpenSSH_MD5": f"MD5: {md5_hex}",
            "OpenSSH_SHA256": f"SHA256:{sha256_b64}"
        }
    except Exception:
        return {}


# =========================
# JWK Conversion
# =========================

def public_key_to_jwk_obj(pub) -> Dict[str, Any]:
    if isinstance(pub, rsa.RSAPublicKey):
        pn = pub.public_numbers()
        n = pn.n.to_bytes((pn.n.bit_length() + 7) // 8, "big")
        e = pn.e.to_bytes((pn.e.bit_length() + 7) // 8, "big")
        return {"kty": "RSA", "n": _b64url_no_pad(n), "e": _b64url_no_pad(e)}
    if isinstance(pub, ec.EllipticCurvePublicKey):
        pn = pub.public_numbers()
        x = pn.x.to_bytes((pn.x.bit_length() + 7) // 8, "big")
        y = pn.y.to_bytes((pn.y.bit_length() + 7) // 8, "big")
        return {"kty": "EC", "crv": pub.curve.name, "x": _b64url_no_pad(x), "y": _b64url_no_pad(y)}
    if isinstance(pub, ed25519.Ed25519PublicKey):
        raw = pub.public_bytes(Encoding.Raw, PublicFormat.Raw)
        return {"kty": "OKP", "crv": "Ed25519", "x": _b64url_no_pad(raw)}
    if isinstance(pub, ed448.Ed448PublicKey):
        raw = pub.public_bytes(Encoding.Raw, PublicFormat.Raw)
        return {"kty": "OKP", "crv": "Ed448", "x": _b64url_no_pad(raw)}
    raise ValueError("Unsupported public key type for JWK")


def private_key_to_jwk_obj(priv, password: Optional[bytes] = None) -> Dict[str, Any]:
    pub = priv.public_key()
    jwk_pub = public_key_to_jwk_obj(pub)
    if isinstance(priv, rsa.RSAPrivateKey):
        numbers = priv.private_numbers()
        d = numbers.d.to_bytes((numbers.d.bit_length() + 7) // 8, "big")
        jwk_pub["d"] = _b64url_no_pad(d)
        # optional CRT params could be added if needed
        return jwk_pub
    if isinstance(priv, ec.EllipticCurvePrivateKey):
        d = numbers_to_bytes = priv.private_numbers().private_value.to_bytes((priv.key_size + 7) // 8, "big")
        jwk_pub["d"] = _b64url_no_pad(numbers_to_bytes)
        return jwk_pub
    if isinstance(priv, ed25519.Ed25519PrivateKey):
        raw = priv.private_bytes(Encoding.Raw, PrivateFormat.Raw, NoEncryption())
        jwk_pub["d"] = _b64url_no_pad(raw)
        return jwk_pub
    if isinstance(priv, ed448.Ed448PrivateKey):
        raw = priv.private_bytes(Encoding.Raw, PrivateFormat.Raw, NoEncryption())
        jwk_pub["d"] = _b64url_no_pad(raw)
        return jwk_pub
    raise ValueError("Unsupported private key type for JWK")


def jwk_to_public_key_obj(jwk_dict: Dict[str, Any]):
    kty = jwk_dict.get("kty")
    if kty == "RSA":
        n = int.from_bytes(base64.urlsafe_b64decode(jwk_dict["n"] + "=="), "big")
        e = int.from_bytes(base64.urlsafe_b64decode(jwk_dict["e"] + "=="), "big")
        pn = rsa.RSAPublicNumbers(e, n)
        return pn.public_key()
    if kty == "EC":
        crv = jwk_dict["crv"]
        curve_cls = getattr(ec, crv.upper(), None)
        if curve_cls is None:
            # map common names
            name_map = {"secp256r1": ec.SECP256R1, "secp384r1": ec.SECP384R1, "secp521r1": ec.SECP521R1}
            curve_cls = name_map.get(crv, None)
        if curve_cls is None:
            raise ValueError(f"Unsupported curve {crv}")
        x = int.from_bytes(base64.urlsafe_b64decode(jwk_dict["x"] + "=="), "big")
        y = int.from_bytes(base64.urlsafe_b64decode(jwk_dict["y"] + "=="), "big")
        pn = ec.EllipticCurvePublicNumbers(x, y, curve_cls())
        return pn.public_key()
    if kty == "OKP" and jwk_dict.get("crv") == "Ed25519":
        x = base64.urlsafe_b64decode(jwk_dict["x"] + "==")
        return ed25519.Ed25519PublicKey.from_public_bytes(x)
    raise ValueError("Unsupported JWK for public key")


# =========================
# Analyze & Convert
# =========================

def analyze_bytes(raw: bytes, filename: str = "input", password: Optional[str] = None) -> Dict[str, Any]:
    text = None
    try:
        text = raw.decode("utf-8")
    except Exception:
        text = None

    out: Dict[str, Any] = {
        "file": filename,
        "type": None,
        "details": {},
        "fingerprints": compute_fingerprints(raw),
        "jwk": {},
        "cert_chain": [],
        "revocation": None,
        "guidance": {},
    }

    # 0) Try PKCS#12
    if password is not None: # Try even with empty password
        try:
            pass_bytes = password.encode()
            p12 = serialization.load_pkcs12(raw, pass_bytes)
            priv, cert, chain = p12.key, p12.cert, p12.ca_certs

            if priv:
                out["type"] = "PKCS#12 Archive"

                # Analyze the private key
                priv_details = {}
                if isinstance(priv, rsa.RSAPrivateKey):
                    priv_details = {"algorithm": "RSA", "key_size": priv.key_size, "security": estimate_security(priv.key_size, "RSA")}
                elif isinstance(priv, ec.EllipticCurvePrivateKey):
                    priv_details = {"algorithm": "EC", "curve": priv.curve.name, "key_size": priv.key_size, "security": estimate_security(priv.key_size, "EC")}

                # Analyze the main certificate
                cert_details = {}
                if cert:
                    cert_details = {
                        "subject": cert.certificate.subject.rfc4514_string(),
                        "issuer": cert.certificate.issuer.rfc4514_string(),
                        "serial_number": hex(cert.certificate.serial_number),
                        "not_before": str(cert.certificate.not_valid_before),
                        "not_after": str(cert.certificate.not_valid_after),
                    }

                # Combine details
                out["details"] = {
                    "archive_contents": {
                        "private_key": priv_details,
                        "certificate": cert_details if cert else "Not present",
                        "additional_certs_count": len(chain)
                    }
                }

                # Get JWK from private key
                out["jwk"] = private_key_to_jwk_obj(priv)

                # Build cert chain display from friendly names
                full_chain_names = []
                if cert: full_chain_names.append(cert.friendly_name.decode() if cert.friendly_name else 'Unnamed Certificate')
                for c in chain: full_chain_names.append(c.friendly_name.decode() if c.friendly_name else 'Unnamed CA Certificate')
                out["cert_chain"] = full_chain_names

                # Add guidance
                out["guidance"] = {
                    "note": "محتویات فایل PKCS#12 با موفقیت استخراج شد.",
                    "openssl_export_key": f"openssl pkcs12 -in {filename} -nocerts -out private_key.pem -nodes -password pass:{password}",
                    "openssl_export_cert": f"openssl pkcs12 -in {filename} -nokeys -clcerts -out certificate.pem -password pass:{password}",
                    "openssl_export_chain": f"openssl pkcs12 -in {filename} -nokeys -cacerts -out chain.pem -password pass:{password}"
                }

                return out
        except Exception:
            # Could be wrong password or not a p12 file. Silently fail and try other formats.
            # We might want to add a message if a password was provided but failed.
            out["guidance"] = {"note": "رمز عبور برای فایل PKCS#12 اشتباه است یا فایل فرمت دیگری دارد."}


    # 1) Try Private Key (PEM)
    if text and "BEGIN" in text and "PRIVATE KEY" in text:
        try:
            priv = serialization.load_pem_private_key(raw, password=None)
            out["type"] = "Private Key"
            if isinstance(priv, rsa.RSAPrivateKey):
                out["details"] = {"algorithm": "RSA", "key_size": priv.key_size, "security": estimate_security(priv.key_size, "RSA")}
            elif isinstance(priv, ec.EllipticCurvePrivateKey):
                out["details"] = {"algorithm": "EC", "curve": priv.curve.name, "key_size": priv.key_size, "security": estimate_security(priv.key_size, "EC")}
            elif isinstance(priv, ed25519.Ed25519PrivateKey):
                out["details"] = {"algorithm": "Ed25519", "key_size": 256, "security": "Strong"}
            elif isinstance(priv, ed448.Ed448PrivateKey):
                out["details"] = {"algorithm": "Ed448", "key_size": 456, "security": "Strong"}
            out["jwk"] = private_key_to_jwk_obj(priv)
            # guidance (OpenSSL) + internal generation pointers
            out["guidance"] = {
                "create_csr_openssl": f"openssl req -new -key {filename} -out request.csr -subj \"/C=IR/ST=Tehran/L=Tehran/O=MyOrg/OU=IT/CN=example.com\"",
                "create_selfsigned_openssl": f"openssl req -x509 -new -key {filename} -days 365 -sha256 -out cert.pem -subj \"/C=IR/ST=Tehran/L=Tehran/O=MyOrg/OU=IT/CN=example.com\"",
                "convert_pkcs8_unencrypted": f"openssl pkcs8 -topk8 -in {filename} -out key_pkcs8.pem -nocrypt",
                "convert_der": f"openssl pkey -in {filename} -outform DER -out key.der",
                "to_public_pem": f"openssl pkey -in {filename} -pubout -out public.pem",
            }
            return out
        except Exception:
            pass

    # 2) Try Public Key (PEM)
    if text and "BEGIN" in text and "PUBLIC KEY" in text:
        try:
            pub = serialization.load_pem_public_key(raw)
            out["type"] = "Public Key"
            if isinstance(pub, rsa.RSAPublicKey):
                out["details"] = {"algorithm": "RSA", "key_size": pub.key_size, "security": estimate_security(pub.key_size, "RSA")}
            elif isinstance(pub, ec.EllipticCurvePublicKey):
                out["details"] = {"algorithm": "EC", "curve": pub.curve.name, "key_size": pub.key_size, "security": estimate_security(pub.key_size, "EC")}
            elif isinstance(pub, ed25519.Ed25519PublicKey):
                out["details"] = {"algorithm": "Ed25519", "key_size": 256, "security": "Strong"}
            elif isinstance(pub, ed448.Ed448PublicKey):
                out["details"] = {"algorithm": "Ed448", "key_size": 456, "security": "Strong"}
            out["jwk"] = public_key_to_jwk_obj(pub)
            out["guidance"] = {
                "make_selfsigned_from_priv": "برای ساخت سرتیفیکیت نیاز به کلید خصوصی دارید. ابتدا Private Key را آپلود کنید یا مسیر آن را بدهید."
            }
            return out
        except Exception:
            pass

    # 3) Try Certificate (PEM)
    if text and "BEGIN CERTIFICATE" in text:
        try:
            # could be chain; parse all
            blocks = pem_blocks(text, "CERTIFICATE")
            certs = [x509.load_pem_x509_certificate(b.encode("utf-8")) for b in blocks]
            leaf = certs[0]
            out["type"] = "X.509 Certificate"
            pub = leaf.public_key()
            details = {
                "subject": leaf.subject.rfc4514_string(),
                "issuer": leaf.issuer.rfc4514_string(),
                "serial_number": hex(leaf.serial_number),
                "not_before": str(leaf.not_valid_before),
                "not_after": str(leaf.not_valid_after),
            }
            if isinstance(pub, rsa.RSAPublicKey):
                details.update({"algorithm": "RSA", "key_size": pub.key_size, "security": estimate_security(pub.key_size, "RSA")})
            elif isinstance(pub, ec.EllipticCurvePublicKey):
                details.update({"algorithm": "EC", "curve": pub.curve.name, "key_size": pub.key_size, "security": estimate_security(pub.key_size, "EC")})
            elif isinstance(pub, ed25519.Ed25519PublicKey):
                details.update({"algorithm": "Ed25519", "key_size": 256, "security": "Strong"})

            out["details"] = details
            out["jwk"] = public_key_to_jwk_obj(pub)
            out["cert_chain"] = [c.subject.rfc4514_string() for c in certs]

            # Revocation placeholder (expose AIA/CRL/OCSP URLs if present)
            aia = []
            try:
                aia_ext = leaf.extensions.get_extension_for_class(x509.AuthorityInformationAccess)
                for ad in aia_ext.value:
                    if ad.access_method.dotted_string in ("1.3.6.1.5.5.7.48.1",):  # OCSP
                        aia.append({"OCSP": ad.access_location.value})
                    if ad.access_method.dotted_string in ("1.3.6.1.5.5.7.48.2",):  # CA Issuers
                        aia.append({"CAIssuers": ad.access_location.value})
            except Exception:
                pass
            crl_dp = []
            try:
                crl_ext = leaf.extensions.get_extension_for_class(x509.CRLDistributionPoints)
                for dp in crl_ext.value:
                    for name in (dp.full_name or []):
                        crl_dp.append(name.value)
            except Exception:
                pass
            out["revocation"] = {
                "ocsp_urls": aia,
                "crl_distribution_points": crl_dp,
                "status": "Unknown (OCSP/CRL شبکه‌ای پیاده‌سازی نشده؛ URLها در بالا آمده است)"
            }
            out["guidance"] = {
                "verify_with_chain": "openssl verify -CAfile chain.pem certificate.pem",
                "openssl_print": "openssl x509 -in certificate.pem -noout -text"
            }
            return out
        except Exception:
            pass

    # 4) Try SSH Public Key
    if text and (text.strip().startswith("ssh-") or text.strip().startswith("ecdsa-") or text.strip().startswith("sk-")):
        try:
            ssh_pub = load_ssh_public_key(raw)
            out["type"] = "SSH Public Key"
            if isinstance(ssh_pub, rsa.RSAPublicKey):
                out["details"] = {"algorithm": "RSA", "key_size": ssh_pub.key_size}
            elif isinstance(ssh_pub, ec.EllipticCurvePublicKey):
                out["details"] = {"algorithm": "EC", "curve": ssh_pub.curve.name, "key_size": ssh_pub.key_size}
            else:
                out["details"] = {"algorithm": ssh_pub.__class__.__name__}
            out["jwk"] = public_key_to_jwk_obj(ssh_pub)
            out["fingerprints"].update(ssh_fingerprints_from_openssh_pub_line(text.strip()))
            return out
        except Exception:
            pass

    out["type"] = "Unknown"
    out["guidance"] = {"note": "نوع ورودی تشخیص داده نشد. مطمئن شوید PEM/SSH/CERT معتبر ارائه می‌دهید."}
    return out


def convert_formats_from_priv(priv_pem: bytes, passphrase: Optional[str] = None) -> Dict[str, bytes]:
    """Given a PEM private key, produce DER, PKCS8 (enc/unencrypted), and public forms."""
    priv = serialization.load_pem_private_key(priv_pem, password=(passphrase.encode() if passphrase else None))
    out: Dict[str, bytes] = {}

    # PEM (as-is normalized)
    out["private_pem"] = priv.private_bytes(Encoding.PEM, PrivateFormat.TraditionalOpenSSL, NoEncryption())

    # PKCS#8 (no password)
    out["private_pkcs8_pem"] = priv.private_bytes(Encoding.PEM, PrivateFormat.PKCS8, NoEncryption())

    # PKCS#8 (encrypted) if passphrase given
    if passphrase:
        out["private_pkcs8_enc_pem"] = priv.private_bytes(
            Encoding.PEM, PrivateFormat.PKCS8, BestAvailableEncryption(passphrase.encode())
        )

    # DER (unencrypted)
    out["private_der"] = priv.private_bytes(Encoding.DER, PrivateFormat.TraditionalOpenSSL, NoEncryption())

    # Public PEM & OpenSSH
    pub = priv.public_key()
    out["public_pem"] = pub.public_bytes(Encoding.PEM, PublicFormat.SubjectPublicKeyInfo)
    try:
        out["public_ssh"] = pub.public_bytes(Encoding.OpenSSH, PublicFormat.OpenSSH)
    except Exception:
        pass

    return out


def match_private_with_certificate(priv_pem: bytes, cert_pem: bytes) -> bool:
    priv = serialization.load_pem_private_key(priv_pem, password=None)
    cert = x509.load_pem_x509_certificate(cert_pem)
    return pubkeys_equal(priv.public_key(), cert.public_key())


def generate_csr_from_priv(priv_pem: bytes, subject_cn: str = "example.com", san_dns: Optional[List[str]] = None) -> bytes:
    priv = serialization.load_pem_private_key(priv_pem, password=None)
    name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, subject_cn)])
    builder = x509.CertificateSigningRequestBuilder().subject_name(name)
    if san_dns:
        builder = builder.add_extension(
            x509.SubjectAlternativeName([x509.DNSName(d) for d in san_dns]), critical=False
        )
    csr = builder.sign(priv, hashes.SHA256())
    return csr.public_bytes(Encoding.PEM)


def generate_selfsigned_from_priv(priv_pem: bytes, subject_cn: str = "example.com", days: int = 365, san_dns: Optional[List[str]] = None) -> bytes:
    priv = serialization.load_pem_private_key(priv_pem, password=None)
    subject = issuer = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, subject_cn)])
    now = datetime.utcnow()
    builder = (
        x509.CertificateBuilder()
        .subject_name(subject)
        .issuer_name(issuer)
        .public_key(priv.public_key())
        .serial_number(x509.random_serial_number())
        .not_valid_before(now - timedelta(minutes=1))
        .not_valid_after(now + timedelta(days=days))
    )
    if san_dns:
        builder = builder.add_extension(
            x509.SubjectAlternativeName([x509.DNSName(d) for d in san_dns]), critical=False
        )
    builder = builder.add_extension(x509.BasicConstraints(ca=False, path_length=None), critical=True)
    cert = builder.sign(private_key=priv, algorithm=hashes.SHA256())
    return cert.public_bytes(Encoding.PEM)


def generate_private_key(key_type: str, rsa_key_size: int = 2048, ec_curve: str = "SECP384R1") -> bytes:
    """Generates an RSA, EC, or Edwards-curve private key and returns it as PEM bytes."""
    if key_type == "rsa":
        private_key = rsa.generate_private_key(
            public_exponent=65537,
            key_size=rsa_key_size,
        )
    elif key_type == "ec":
        curve_obj = getattr(ec, ec_curve.upper())()
        private_key = ec.generate_private_key(curve_obj)
    elif key_type == "ed25519":
        private_key = ed25519.Ed25519PrivateKey.generate()
    elif key_type == "ed448":
        private_key = ed448.Ed448PrivateKey.generate()
    else:
        raise ValueError(f"Unsupported key type: {key_type}")

    return private_key.private_bytes(
        encoding=Encoding.PEM,
        format=PrivateFormat.PKCS8,
        encryption_algorithm=NoEncryption(),
    )


def update_key_password(key_pem: bytes, current_pass: Optional[str], new_pass: Optional[str]) -> bytes:
    """Loads a private key and re-serializes it with a new password or none."""
    current_pass_bytes = current_pass.encode() if current_pass else None

    # Load the private key with its current password
    private_key = serialization.load_pem_private_key(
        key_pem,
        password=current_pass_bytes
    )

    # Determine the new encryption type
    if new_pass:
        encryption_algorithm = BestAvailableEncryption(new_pass.encode())
    else:
        encryption_algorithm = NoEncryption()

    # Re-serialize the key with the new encryption
    return private_key.private_bytes(
        encoding=Encoding.PEM,
        format=PrivateFormat.PKCS8,
        encryption_algorithm=encryption_algorithm
    )


def sign_data(key_pem: bytes, password: Optional[str], data: bytes, hash_algo: str, padding_scheme: str) -> bytes:
    """Signs data with a private key and returns the signature."""
    password_bytes = password.encode() if password else None
    private_key = serialization.load_pem_private_key(key_pem, password=password_bytes)

    hash_obj = getattr(hashes, hash_algo.upper())()

    if isinstance(private_key, rsa.RSAPrivateKey):
        if padding_scheme.upper() == 'PSS':
            pad = padding.PSS(mgf=padding.MGF1(hash_obj), salt_length=padding.PSS.MAX_LENGTH)
        elif padding_scheme.upper() == 'PKCS1V15':
            pad = padding.PKCS1v15()
        else:
            raise ValueError("Unsupported padding scheme for RSA")

        signature = private_key.sign(data, pad, hash_obj)
    elif isinstance(private_key, ec.EllipticCurvePrivateKey):
        signature = private_key.sign(data, ec.ECDSA(hash_obj))
    else:
        raise ValueError("Unsupported key type for signing")

    return signature


def verify_signature(pub_key_pem: bytes, signature: bytes, data: bytes, hash_algo: str, padding_scheme: str) -> bool:
    """Verifies a signature with a public key."""
    public_key = load_any_public_key(pub_key_pem)
    if public_key is None:
        # Maybe it's a certificate?
        try:
            cert = x509.load_pem_x509_certificate(pub_key_pem)
            public_key = cert.public_key()
        except Exception:
            raise ValueError("Invalid Public Key or Certificate file")

    hash_obj = getattr(hashes, hash_algo.upper())()

    try:
        if isinstance(public_key, rsa.RSAPublicKey):
            if padding_scheme.upper() == 'PSS':
                pad = padding.PSS(mgf=padding.MGF1(hash_obj), salt_length=padding.PSS.MAX_LENGTH)
            elif padding_scheme.upper() == 'PKCS1V15':
                pad = padding.PKCS1v15()
            else:
                raise ValueError("Unsupported padding scheme")

            public_key.verify(signature, data, pad, hash_obj)
        elif isinstance(public_key, ec.EllipticCurvePublicKey):
            public_key.verify(signature, data, ec.ECDSA(hash_obj))
        else:
            raise ValueError("Unsupported key type for verification")

        return True
    except InvalidSignature:
        return False


def encrypt_data(pub_key_pem: bytes, plaintext: bytes) -> bytes:
    """Encrypts data with an RSA public key."""
    public_key = load_any_public_key(pub_key_pem)
    if public_key is None:
        try:
            cert = x509.load_pem_x509_certificate(pub_key_pem)
            public_key = cert.public_key()
        except Exception:
            raise ValueError("Invalid Public Key or Certificate file")

    if not isinstance(public_key, rsa.RSAPublicKey):
        raise TypeError("Encryption is only supported for RSA keys with this tool.")

    ciphertext = public_key.encrypt(
        plaintext,
        padding.OAEP(
            mgf=padding.MGF1(algorithm=hashes.SHA256()),
            algorithm=hashes.SHA256(),
            label=None
        )
    )
    return ciphertext


# =========================
# Flask Web App
# =========================

DOWNLOAD_DIR = "/tmp"
app = Flask(__name__)
app.config["DOWNLOAD_DIR"] = DOWNLOAD_DIR

@app.template_filter('fromjson')
def from_json_filter(value):
    return json.loads(value)

INDEX_HTML = '''
<!doctype html>
<html lang="fa" dir="rtl">
<head>
<meta charset="utf-8">
<title>Enterprise PEM/Certificate Analyzer</title>
<script src="https://cdn.plot.ly/plotly-latest.min.js"></script>
<style>
body{font-family:Tahoma,Arial,sans-serif;max-width:1000px;margin:32px auto;padding:0 16px}
.card{border:1px solid #ddd;border-radius:14px;padding:16px;margin:16px 0;box-shadow:0 2px 10px rgba(0,0,0,.05)}
h2{margin:8px 0}
pre{background:#0b1021;color:#c0e0ff;padding:12px;border-radius:10px;overflow:auto}
label{display:block;margin-top:8px}
input,select,button{padding:8px;border-radius:8px;border:1px solid #ccc}
.btn{background:#2c7be5;color:#fff;border:none;cursor:pointer}
.row{display:grid;grid-template-columns:1fr 1fr;gap:16px}
.small{opacity:.8}
.badge{display:inline-block;padding:4px 10px;border-radius:999px;background:#eee;margin:2px}
.badge.green{background:#e7f8ed;color:#0b7a35}
.badge.orange{background:#fff5e6;color:#975a00}
.badge.red{background:#fdecea;color:#a30000}
.styled-table{border-collapse:collapse;margin:25px 0;font-size:.9em;width:100%;box-shadow:0 0 20px rgba(0,0,0,.15)}
.styled-table thead tr{background-color:#2c7be5;color:#fff;text-align:left}
.styled-table th,.styled-table td{padding:12px 15px}
.styled-table tbody tr{border-bottom:1px solid #ddd}
.styled-table tbody tr:nth-of-type(even){background-color:#f3f3f3}
.styled-table tbody tr:last-of-type{border-bottom:2px solid #2c7be5}
.accordion-header{background-color:#f1f1f1;cursor:pointer;padding:12px;border:1px solid #ddd;margin-top:5px;border-radius:8px}
.accordion-header:hover{background-color:#e8e8e8}
.accordion-content{padding:10px 18px;display:none;overflow:hidden;background-color:#fafafa;border:1px solid #ddd;border-top:none;border-radius:0 0 8px 8px}
</style>
</head>
<body>
<h1>Enterprise PEM/Certificate Analyzer</h1>

<div class="card">
  <h2>۱) تحلیل کلید/سرتیفیکیت</h2>
  <form method="post" action="/analyze" enctype="multipart/form-data">
    <label>فایل کلید/سرتیفیکیت (PEM, P12, ...):</label>
    <input type="file" name="file" required>
    <label>Password (برای فایل P12/PFX، اختیاری):</label>
    <input type="password" name="password">
    <button class="btn" type="submit">تحلیل</button>
  </form>
</div>

<div class="card">
  <h2>۲) ساخت کلید خصوصی جدید</h2>
  <form method="post" action="/generate">
    <div class="row" onchange="toggleKeyParams()">
      <div>
        <label>نوع کلید:</label>
        <select name="key_type" id="key_type">
          <option value="rsa" selected>RSA</option>
          <option value="ec">Elliptic Curve (EC)</option>
          <option value="ed25519">Ed25519</option>
          <option value="ed448">Ed448</option>
        </select>
      </div>
      <div>
        <div id="rsa_params">
          <label>اندازه کلید (بیت):</label>
          <select name="rsa_key_size">
            <option value="2048">2048</option>
            <option value="3072" selected>3072</option>
            <option value="4096">4096</option>
          </select>
        </div>
        <div id="ec_params" style="display:none;">
          <label>نام منحنی:</label>
          <select name="ec_curve">
            <option value="SECP256R1">SECP256R1 (P-256)</option>
            <option value="SECP384R1">SECP384R1 (P-384)</option>
            <option value="SECP521R1">SECP521R1 (P-521)</option>
            <option value="SECP256K1">SECP256K1 (Bitcoin curve)</option>
          </select>
        </div>
      </div>
    </div>
    <button class="btn" type="submit">ساخت کلید</button>
  </form>
</div>

<div class="card">
  <h2>۳) ایجاد CSR / Self-Signed</h2>
  <form method="post" action="/create_from_priv" enctype="multipart/form-data">
    <label>Private Key (PEM):</label>
    <input type="file" name="priv" required>
    <label>Common Name (CN):</label>
    <input type="text" name="cn" placeholder="example.com">
    <label>SAN (DNS, جداشده با ویرگول):</label>
    <input type="text" name="san" placeholder="www.example.com,api.example.com">
    <div class="row">
      <div><button class="btn" name="action" value="csr" type="submit">ایجاد CSR</button></div>
      <div><button class="btn" name="action" value="self" type="submit">ایجاد Self-Signed</button></div>
    </div>
  </form>
</div>

<div class="card">
  <h2>۴) تبدیل فرمت‌ها</h2>
  <form method="post" action="/convert" enctype="multipart/form-data">
    <label>Private Key (PEM):</label>
    <input type="file" name="priv" required>
    <label>Password برای خروجی PKCS#8 رمزدار (اختیاری):</label>
    <input type="password" name="password" placeholder="optional">
    <button class="btn" type="submit">تبدیل</button>
  </form>
</div>

<div class="card">
  <h2>۵) مدیریت رمز عبور کلید خصوصی</h2>
  <form method="post" action="/manage_password" enctype="multipart/form-data">
    <label>فایل کلید خصوصی (PEM):</label>
    <input type="file" name="priv_key" required>
    <label>رمز عبور فعلی (اگر کلید رمز دارد):</label>
    <input type="password" name="current_pass" placeholder="اختیاری">
    <label>رمز عبور جدید (برای حذف رمز، این فیلد را خالی بگذارید):</label>
    <input type="password" name="new_pass" placeholder="اختیاری">
    <button class="btn" type="submit">اعمال تغییرات</button>
  </form>
</div>

<div class="card">
  <h2>۶) تطبیق Private Key و Certificate</h2>
  <form method="post" action="/match" enctype="multipart/form-data">
    <label>Private Key (PEM):</label>
    <input type="file" name="priv" required>
    <label>Certificate (PEM):</label>
    <input type="file" name="cert" required>
    <button class="btn" type="submit">بررسی تطبیق</button>
  </form>
</div>

<div class="card">
  <h2>۷) امضای دیجیتال داده</h2>
  <form method="post" action="/sign" enctype="multipart/form-data">
    <label>فایل کلید خصوصی (PEM):</label>
    <input type="file" name="priv_key" required>
    <label>رمز عبور کلید خصوصی (اگر وجود دارد):</label>
    <input type="password" name="password">
    <label>داده برای امضا:</label>
    <textarea name="data_to_sign" rows="5" required style="width:100%;box-sizing:border-box;"></textarea>
    <div class="row">
        <div>
            <label>الگوریتم هش:</label>
            <select name="hash_algo">
                <option value="SHA256" selected>SHA-256</option>
                <option value="SHA384">SHA-384</option>
                <option value="SHA512">SHA-512</option>
            </select>
        </div>
        <div>
            <label>Padding (برای RSA):</label>
            <select name="padding_scheme">
                <option value="PSS" selected>PSS</option>
                <option value="PKCS1v15">PKCS1v15</option>
            </select>
        </div>
    </div>
    <button class="btn" type="submit">امضا کن</button>
  </form>
</div>

<div class="card">
  <h2>۸) تایید امضای دیجیتال</h2>
  <form method="post" action="/verify" enctype="multipart/form-data">
    <label>فایل کلید عمومی (PEM, SSH) یا سرتیفیکیت:</label>
    <input type="file" name="pub_key" required>
    <label>داده اصلی (که امضا شده):</label>
    <textarea name="original_data" rows="5" required style="width:100%;box-sizing:border-box;"></textarea>
    <label>امضا (در فرمت Base64):</label>
    <textarea name="signature_b64" rows="3" required style="width:100%;box-sizing:border-box;"></textarea>
    <div class="row">
        <div>
            <label>الگوریتم هش:</label>
            <select name="hash_algo">
                <option value="SHA256" selected>SHA-256</option>
                <option value="SHA384">SHA-384</option>
                <option value="SHA512">SHA-512</option>
            </select>
        </div>
        <div>
            <label>Padding (برای RSA):</label>
            <select name="padding_scheme">
                <option value="PSS" selected>PSS</option>
                <option value="PKCS1v15">PKCS1v15</option>
            </select>
        </div>
    </div>
    <button class="btn" type="submit">تایید امضا</button>
  </form>
</div>

<div class="card">
  <h2>۹) رمزنگاری داده با کلید عمومی</h2>
  <form method="post" action="/encrypt" enctype="multipart/form-data">
    <label>فایل کلید عمومی (PEM) یا سرتیفیکیت (فقط RSA):</label>
    <input type="file" name="pub_key" required>
    <label>داده برای رمزنگاری:</label>
    <textarea name="plaintext" rows="5" required style="width:100%;box-sizing:border-box;"></textarea>
    <label>Padding (فقط برای RSA):</label>
    <select name="padding_scheme">
        <option value="OAEP" selected>OAEP (SHA-256)</option>
    </select>
    <button class="btn" type="submit">رمزنگاری کن</button>
  </form>
</div>

<div class="card small">
  <b>راهنمای OpenSSL:</b>
  <pre>
ساخت CSR:     openssl req -new -key private.pem -out request.csr -subj "/C=IR/ST=Tehran/L=Tehran/O=MyOrg/OU=IT/CN=example.com"
Self-Signed:  openssl req -x509 -new -key private.pem -days 365 -sha256 -out cert.pem -subj "/C=IR/ST=Tehran/L=Tehran/O=MyOrg/OU=IT/CN=example.com"
نمایش سرتیفیکیت: openssl x509 -in cert.pem -noout -text
  </pre>
</div>

{% if result %}
<div class="card">
  <h2>نتیجه</h2>
  {% if result.plot_div %} {{ result.plot_div|safe }} {% endif %}
  {% if result.badge %}
     <span class="badge {{result.badge.color}}">{{result.badge.text}}</span>
  {% endif %}

{% macro render_analysis(res) %}
  <table class="styled-table">
    <tbody>
      <tr><td>Type</td><td>{{ res.type }}</td></tr>
      {% if res.details.algorithm %}<tr><td>Algorithm</td><td>{{ res.details.algorithm }}</td></tr>{% endif %}
      {% if res.details.key_size %}<tr><td>Key Size</td><td>{{ res.details.key_size }} bits</td></tr>{% endif %}
      {% if res.details.curve %}<tr><td>Curve</td><td>{{ res.details.curve }}</td></tr>{% endif %}
      {% if res.details.security %}<tr><td>Security</td><td><span class="badge {{'green' if res.details.security == 'Strong' else ('orange' if res.details.security == 'Medium' else 'red')}}">{{ res.details.security }}</span></td></tr>{% endif %}

      {# Certificate Specific Fields #}
      {% if res.type == "X.509 Certificate" %}
        <tr><td>Subject</td><td><code>{{ res.details.subject }}</code></td></tr>
        <tr><td>Issuer</td><td><code>{{ res.details.issuer }}</code></td></tr>
        <tr><td>Serial Number</td><td><code>{{ res.details.serial_number }}</code></td></tr>
        <tr><td>Valid From</td><td>{{ res.details.not_before }}</td></tr>
        <tr><td>Valid Until</td><td>{{ res.details.not_after }}</td></tr>
      {% endif %}

      {# PKCS#12 Specific Fields #}
      {% if res.type == "PKCS#12 Archive" %}
        <tr><td colspan="2" style="background:#e8f0fe;"><strong>Private Key Details</strong></td></tr>
        <tr><td>Algorithm</td><td>{{ res.details.archive_contents.private_key.algorithm }}</td></tr>
        <tr><td>Key Size/Curve</td><td>{{ res.details.archive_contents.private_key.key_size or res.details.archive_contents.private_key.curve }}</td></tr>
        <tr><td colspan="2" style="background:#e8f0fe;"><strong>Certificate Details</strong></td></tr>
        {% if res.details.archive_contents.certificate != "Not present" %}
          <tr><td>Subject</td><td><code>{{ res.details.archive_contents.certificate.subject }}</code></td></tr>
          <tr><td>Issuer</td><td><code>{{ res.details.archive_contents.certificate.issuer }}</code></td></tr>
        {% else %}
          <tr><td>Certificate</td><td>Not present in archive</td></tr>
        {% endif %}
      {% endif %}

      {# Digital Signature Result #}
      {% if res.type == "Digital Signature" %}
        <tr><td>Signature (Base64)</td><td><textarea readonly rows="5" style="width:100%;box-sizing:border-box;">{{ res.details.signature_base64 }}</textarea></td></tr>
        <tr><td>Note</td><td>{{ res.details.note }}</td></tr>
      {% endif %}

      {# Signature Verification Result #}
      {% if res.type == "Signature Verification" %}
        <tr>
          <td>Verification Result</td>
          <td>
            {% if res.details.is_valid %}
              <span class="badge green" style="font-size:1.1em;">Signature is VALID</span>
            {% else %}
              <span class="badge red" style="font-size:1.1em;">Signature is INVALID</span>
            {% endif %}
          </td>
        </tr>
      {% endif %}

      {# Encryption Result #}
      {% if res.type == "Public Key Encryption" %}
        <tr><td>Ciphertext (Base64)</td><td><textarea readonly rows="5" style="width:100%;box-sizing:border-box;">{{ res.details.ciphertext_base64 }}</textarea></td></tr>
        <tr><td>Note</td><td>{{ res.details.note }}</td></tr>
      {% endif %}
    </tbody>
  </table>

  {% if res.fingerprints %}
    <h4>Fingerprints</h4>
    <pre style="font-size: 1.1em;">MD5:   {{ res.fingerprints.MD5.split(': ')[1] }}
SHA1:  {{ res.fingerprints.SHA1.split(': ')[1] }}
SHA256:{{ res.fingerprints.SHA256.split(': ')[1] }}{% if res.fingerprints.OpenSSH_SHA256 %}\nOpenSSH (SHA256): {{ res.fingerprints.OpenSSH_SHA256 }}{% endif %}</pre>
  {% endif %}

  {% if res.cert_chain %}
    <h4>Certificate Chain ({{ res.cert_chain|length }} certs)</h4>
    <ol style="font-size:0.9em; max-height:150px; overflow:auto; border:1px solid #ddd; padding:10px 10px 10px 30px; border-radius:8px;">
    {% for item in res.cert_chain %}
      <li><code>{{ item }}</code></li>
    {% endfor %}
    </ol>
  {% endif %}

  {% if res.guidance %}
    <h4>Guidance & Raw Data</h4>
    <details>
        <summary>Click to view guidance and raw JSON data</summary>
        <pre>{{ res | tojson(indent=2) }}</pre>
    </details>
  {% endif %}
{% endmacro %}

{# Main result rendering logic #}
{% set data = result.json | fromjson %}
{% if data.type == "Batch Analysis (Zip)" %}
  <h4>Batch Analysis for: <code>{{ data.file }}</code></h4>
  {% for item in data.batch_results %}
    <div class="accordion-item">
      <h4 class="accordion-header">{{ item.file }} ({{ item.type }})</h4>
      <div class="accordion-content">
        {{ render_analysis(item) }}
      </div>
    </div>
  {% endfor %}
{% else %}
  <h4>Analysis for: <code>{{ data.file }}</code></h4>
  {{ render_analysis(data) }}
{% endif %}
  {% if result.download_name %}
    <p><a class="btn" href="/download?filename={{ result.download_path }}&name={{ result.download_name }}">دانلود خروجی</a></p>
  {% endif %}
  {% if result.report_html or result.report_md %}
    {% if result.report_html %}<p><a class="btn" href="/download?filename={{ result.report_html }}&name=report.html">دانلود گزارش HTML</a></p>{% endif %}
    {% if result.report_md %}<p><a class="btn" href="/download?filename={{ result.report_md }}&name=report.md">دانلود گزارش Markdown</a></p>{% endif %}
  {% endif %}
</div>
{% endif %}

<script>
function toggleKeyParams() {
  var key_type = document.getElementById('key_type').value;
  var rsa_params = document.getElementById('rsa_params');
  var ec_params = document.getElementById('ec_params');

  // Hide all by default
  rsa_params.style.display = 'none';
  ec_params.style.display = 'none';

  if (key_type === 'rsa') {
    rsa_params.style.display = 'block';
  } else if (key_type === 'ec') {
    ec_params.style.display = 'block';
  }
  // For Ed25519 and Ed448, both remain hidden as they have no parameters.
}
document.addEventListener('DOMContentLoaded', function() {
    toggleKeyParams();
    setupAccordion();
});

function setupAccordion() {
    var acc = document.getElementsByClassName("accordion-header");
    for (var i = 0; i < acc.length; i++) {
        acc[i].addEventListener("click", function() {
            this.classList.toggle("active");
            var content = this.nextElementSibling;
            if (content.style.display === "block") {
                content.style.display = "none";
            } else {
                content.style.display = "block";
            }
        });
    }
}
</script>

</body>
</html>
'''

def _pie_div(security: Optional[str]) -> str:
    labels = ['Weak', 'Medium', 'Strong']
    values = [1 if security=='Weak' else 0,
              1 if security=='Medium' else 0,
              1 if security=='Strong' else 0]
    fig = go.Figure(data=[go.Pie(labels=labels, values=values, hole=.35)])
    return pyo.plot(fig, output_type='div', include_plotlyjs=False)


def _make_report_files(data: Dict[str, Any]) -> Tuple[Optional[str], Optional[str]]:
    ts = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    html_path = f"/tmp/report_{ts}.html"
    md_path   = f"/tmp/report_{ts}.md"
    title = f"Analysis Report — {data.get('file','input')}"
    # HTML
    with open(html_path, "w", encoding="utf-8") as f:
        f.write(f"<h2>{title}</h2>")
        f.write("<pre style='background:#0b1021;color:#c0e0ff;padding:12px;border-radius:10px;'>")
        f.write(json.dumps(data, indent=2, ensure_ascii=False))
        f.write("</pre>")
    # MD
    with open(md_path, "w", encoding="utf-8") as f:
        f.write(f"# {title}\n\n")
        f.write("```json\n")
        f.write(json.dumps(data, indent=2, ensure_ascii=False))
        f.write("\n```\n")
    return html_path, md_path


@app.route("/", methods=["GET"])
def index():
    return render_template_string(INDEX_HTML)


def _render_analysis_result(data: Dict[str, Any]) -> str:
    """Renders the analysis result to the main template."""
    pie_div = ""
    # Pie charts don't make sense for batch results, only for single-file security estimates.
    if data.get("type") != "Batch Analysis (Zip)":
        pie_div = _pie_div(data.get("details", {}).get("security"))

    html_report, md_report = _make_report_files(data)
    badge = None
    sec = data.get("details", {}).get("security")

    # Special badge for batch results
    if data.get("type") == "Batch Analysis (Zip)":
        badge = {"text": f"{data['details']['file_count']} فایل تحلیل شد", "color": "green"}
    elif sec == "Strong":
        badge = {"text": "امنیت قوی", "color": "green"}
    elif sec == "Medium":
        badge = {"text": "امنیت متوسط", "color": "orange"}
    elif sec == "Weak":
        badge = {"text": "امنیت ضعیف", "color": "red"}

    result = {
        "plot_div": pie_div,
        "json": json.dumps(data, indent=2, ensure_ascii=False),
        "badge": badge,
        "report_html": os.path.basename(html_report) if html_report else None,
        "report_md": os.path.basename(md_report) if md_report else None,
        "download_name": None,
        "download_path": None,
    }
    return render_template_string(INDEX_HTML, result=result)


@app.route("/analyze", methods=["POST"])
def route_analyze():
    file = request.files.get("file")
    password = request.form.get("password") or None
    raw = file.read()
    filename = file.filename

    # Check for zip file
    if filename.lower().endswith(".zip"):
        results = []
        try:
            with zipfile.ZipFile(io.BytesIO(raw)) as zf:
                for info in zf.infolist():
                    if info.is_dir() or info.filename.startswith('__MACOSX'):
                        continue # Skip directories and macosx metadata

                    file_content = zf.read(info.filename)
                    analysis = analyze_bytes(file_content, filename=info.filename, password=password)
                    results.append(analysis)

            # Format a batch result
            data = {
                "file": filename,
                "type": "Batch Analysis (Zip)",
                "details": {
                    "file_count": len(results),
                    "files_analyzed": [res["file"] for res in results]
                },
                "batch_results": results
            }
            return _render_analysis_result(data)

        except zipfile.BadZipFile:
            return "فایل Zip آپلود شده معتبر نیست.", 400
        except Exception as e:
            return f"خطا در پردازش فایل Zip: {e}", 500

    # If not a zip file, proceed with single file analysis
    data = analyze_bytes(raw, filename=filename, password=password)
    return _render_analysis_result(data)


@app.route("/generate", methods=["POST"])
def route_generate():
    key_type = request.form.get("key_type")

    try:
        if key_type == "rsa":
            rsa_key_size = int(request.form.get("rsa_key_size", 2048))
            key_pem = generate_private_key(key_type="rsa", rsa_key_size=rsa_key_size)
            out_name = f"rsa_{rsa_key_size}_private_key.pem"
        elif key_type == "ec":
            ec_curve = request.form.get("ec_curve", "SECP384R1")
            key_pem = generate_private_key(key_type="ec", ec_curve=ec_curve)
            out_name = f"ec_{ec_curve}_private_key.pem"
        elif key_type in ("ed25519", "ed448"):
            key_pem = generate_private_key(key_type=key_type)
            out_name = f"{key_type}_private_key.pem"
        else:
            return "Invalid key type", 400
    except Exception as e:
        # Handle potential errors during key generation, e.g., invalid curve name
        return f"Error generating key: {e}", 500


    # Save the key for download
    path = os.path.join(app.config["DOWNLOAD_DIR"], out_name)
    with open(path, "wb") as f:
        f.write(key_pem)

    res = {
        "status": "ok",
        "action": "generate",
        "key_type": key_type,
        "note": f"کلید خصوصی جدید در فایل {out_name} ایجاد شد و آماده دانلود است.",
    }
    html_report, md_report = _make_report_files(res)

    result = {
        "plot_div": "",
        "json": json.dumps(res, indent=2, ensure_ascii=False),
        "badge": {"text": "کلید ایجاد شد", "color": "green"},
        "report_html": os.path.basename(html_report) if html_report else None,
        "report_md": os.path.basename(md_report) if md_report else None,
        "download_name": out_name,
        "download_path": out_name, # This is the filename for the template
    }
    return render_template_string(INDEX_HTML, result=result)


@app.route("/create_from_priv", methods=["POST"])
def route_create_from_priv():
    file = request.files.get("priv")
    raw = file.read()
    action = request.form.get("action")
    cn = request.form.get("cn") or "example.com"
    san_raw = (request.form.get("san") or "").strip()
    san_list = [s.strip() for s in san_raw.split(",") if s.strip()] or None

    out_bytes = b""
    out_name = None
    if action == "csr":
        out_bytes = generate_csr_from_priv(raw, subject_cn=cn, san_dns=san_list)
        out_name = "request.csr"
    else:
        out_bytes = generate_selfsigned_from_priv(raw, subject_cn=cn, days=365, san_dns=san_list)
        out_name = "selfsigned.pem"

    # Build minimal JSON result:
    res = {
        "status": "ok",
        "action": action,
        "cn": cn,
        "san": san_list,
        "note": "فایل خروجی جهت دانلود فراهم شده است.",
    }
    pie_div = ""  # not relevant here
    html_report, md_report = _make_report_files(res)

    # persist output
    path = f"/tmp/{out_name}"
    with open(path, "wb") as f:
        f.write(out_bytes)

    result = {
        "plot_div": pie_div,
        "json": json.dumps(res, indent=2, ensure_ascii=False),
        "badge": {"text": "ایجاد شد", "color": "green"},
        "report_html": os.path.basename(html_report) if html_report else None,
        "report_md": os.path.basename(md_report) if md_report else None,
        "download_name": out_name,
        "download_path": out_name,
    }
    return render_template_string(INDEX_HTML, result=result)


@app.route("/convert", methods=["POST"])
def route_convert():
    file = request.files.get("priv")
    password = request.form.get("password") or None
    raw = file.read()
    try:
        outputs = convert_formats_from_priv(raw, passphrase=password)
    except Exception as e:
        return f"Error during conversion: {e}", 500

    manifest = {}
    for name, content in outputs.items():
        out_name = f"{name}.{'pem' if name.endswith('_pem') or 'public_pem' in name else 'bin'}"
        if name == "private_der": out_name = "private.der"
        if name == "public_pem":  out_name = "public.pem"
        if name == "public_ssh":  out_name = "public_ssh.pub"
        full = os.path.join(app.config["DOWNLOAD_DIR"], out_name)
        with open(full, "wb") as f:
            f.write(content)
        manifest[name] = out_name

    res = {
        "type": "Format Conversion",
        "details": {
            "artifacts": manifest,
            "note": "Conversion successful. Individual files can be downloaded from the report."
        },
        "file": file.filename,
        "fingerprints": None, "cert_chain": None, "guidance": None, "jwk": None
    }
    return _render_analysis_result(res)


@app.route("/manage_password", methods=["POST"])
def route_manage_password():
    file = request.files.get("priv_key")
    if not file:
        return "Private key file not provided", 400

    key_pem = file.read()
    current_pass = request.form.get("current_pass") or None
    new_pass = request.form.get("new_pass") or None

    try:
        new_key_pem = update_key_password(key_pem, current_pass, new_pass)
    except (ValueError, TypeError):
        # ValueError for wrong password, TypeError if key is public
        return "رمز عبور فعلی اشتباه است یا فایل کلید خصوصی معتبر نیست.", 400
    except Exception as e:
        return f"An unexpected error occurred: {e}", 500

    # Save the new key for download
    out_name = "private_key_updated.pem"
    path = os.path.join(app.config["DOWNLOAD_DIR"], out_name)
    with open(path, "wb") as f:
        f.write(new_key_pem)

    res = {
        "status": "ok",
        "action": "manage_password",
        "note": f"عملیات با موفقیت انجام شد. کلید جدید در فایل {out_name} آماده دانلود است.",
    }

    result = {
        "plot_div": "",
        "json": json.dumps(res, indent=2, ensure_ascii=False),
        "badge": {"text": "رمز عبور به‌روز شد", "color": "green"},
        "report_html": None,
        "report_md": None,
        "download_name": out_name,
        "download_path": out_name,
    }
    return render_template_string(INDEX_HTML, result=result)


@app.route("/sign", methods=["POST"])
def route_sign():
    file = request.files.get("priv_key")
    password = request.form.get("password") or None
    data_to_sign = request.form.get("data_to_sign", "").encode()
    hash_algo = request.form.get("hash_algo", "SHA256")
    padding_scheme = request.form.get("padding_scheme", "PSS")

    if not file or not data_to_sign:
        return "Private key or data to sign not provided", 400

    key_pem = file.read()

    try:
        signature = sign_data(key_pem, password, data_to_sign, hash_algo, padding_scheme)
        signature_b64 = base64.b64encode(signature).decode('ascii')
    except Exception as e:
        return f"Error during signing: {e}", 500

    res = {
        "type": "Digital Signature",
        "details": {
            "signature_base64": signature_b64,
            "note": "Data signed successfully."
        },
        "file": file.filename,
        "fingerprints": None,
        "cert_chain": None,
        "guidance": None,
        "jwk": None
    }

    return _render_analysis_result(res)


@app.route("/verify", methods=["POST"])
def route_verify():
    pub_key_file = request.files.get("pub_key")
    original_data = request.form.get("original_data", "").encode()
    signature_b64 = request.form.get("signature_b64", "")
    hash_algo = request.form.get("hash_algo", "SHA256")
    padding_scheme = request.form.get("padding_scheme", "PSS")

    if not pub_key_file or not original_data or not signature_b64:
        return "Public key, data, or signature not provided", 400

    pub_key_pem = pub_key_file.read()
    try:
        signature = base64.b64decode(signature_b64)
    except Exception:
        return "Signature is not valid Base64", 400

    try:
        is_valid = verify_signature(pub_key_pem, signature, original_data, hash_algo, padding_scheme)
    except Exception as e:
        return f"Error during verification: {e}", 500

    res = {
        "type": "Signature Verification",
        "details": {
            "is_valid": is_valid,
            "status_text": "VALID" if is_valid else "INVALID"
        },
        "file": pub_key_file.filename,
        "fingerprints": None,
        "cert_chain": None,
        "guidance": None,
        "jwk": None
    }

    return _render_analysis_result(res)


@app.route("/encrypt", methods=["POST"])
def route_encrypt():
    pub_key_file = request.files.get("pub_key")
    plaintext = request.form.get("plaintext", "").encode()

    if not pub_key_file or not plaintext:
        return "Public key or plaintext not provided", 400

    pub_key_pem = pub_key_file.read()

    try:
        ciphertext = encrypt_data(pub_key_pem, plaintext)
        ciphertext_b64 = base64.b64encode(ciphertext).decode('ascii')
    except Exception as e:
        return f"Error during encryption: {e}", 500

    res = {
        "type": "Public Key Encryption",
        "details": {
            "ciphertext_base64": ciphertext_b64,
            "note": "Data encrypted successfully."
        },
        "file": pub_key_file.filename,
        "fingerprints": None,
        "cert_chain": None,
        "guidance": None,
        "jwk": None
    }

    return _render_analysis_result(res)


@app.route("/match", methods=["POST"])
def route_match():
    priv_file = request.files.get("priv")
    cert_file = request.files.get("cert")
    priv = priv_file.read()
    cert = cert_file.read()
    ok = False
    err = None
    try:
        ok = match_private_with_certificate(priv, cert)
    except Exception as e:
        err = str(e)

    data = {
        "type": "Key/Cert Match",
        "details": {
            "match": bool(ok),
            "error": err,
            "status_text": "✅ Keys MATCH" if ok else "❌ Keys DO NOT MATCH"
        },
        "file": f"{priv_file.filename} vs {cert_file.filename}",
        "fingerprints": None, "cert_chain": None, "guidance": None, "jwk": None
    }
    return _render_analysis_result(data)


@app.route("/download", methods=["GET"])
def route_download():
    filename = request.args.get("filename")
    name = request.args.get("name") or filename
    if not filename:
        return "filename not specified", 400

    filename = secure_filename(filename)
    return send_from_directory(app.config["DOWNLOAD_DIR"], filename, as_attachment=True, download_name=name)


# =========================
# CLI (optional)
# =========================

def cli():
    import argparse
    p = argparse.ArgumentParser(description="Enterprise PEM/Certificate Analyzer")
    sub = p.add_subparsers(dest="cmd")

    a = sub.add_parser("analyze", help="Analyze a PEM/SSH/Cert file")
    a.add_argument("file")

    c = sub.add_parser("convert", help="Convert formats from Private Key (PEM)")
    c.add_argument("priv")
    c.add_argument("--password")

    m = sub.add_parser("match", help="Match private key with certificate")
    m.add_argument("priv")
    m.add_argument("cert")

    g = sub.add_parser("gen", help="Generate CSR or Self-Signed from private key")
    g.add_argument("priv")
    g.add_argument("--cn", default="example.com")
    g.add_argument("--san", default="")
    g.add_argument("--self", action="store_true", help="Generate self-signed instead of CSR")

    j = sub.add_parser("pem2jwk", help="Convert PEM (public/private) to JWK")
    j.add_argument("pem")

    w = sub.add_parser("web", help="Run Web Dashboard")
    w.add_argument("--host", default="127.0.0.1")
    w.add_argument("--port", default=5000, type=int)
    w.add_argument("--debug", action="store_true")

    args = p.parse_args()
    if args.cmd == "analyze":
        with open(args.file, "rb") as f:
            raw = f.read()
        res = analyze_bytes(raw, filename=args.file)
        print(json.dumps(res, indent=2, ensure_ascii=False))
    elif args.cmd == "convert":
        with open(args.priv, "rb") as f:
            priv = f.read()
        outs = convert_formats_from_priv(priv, passphrase=args.password)
        for k, v in outs.items():
            out_name = f"{k}.pem" if k.endswith("_pem") else ( "private.der" if k=="private_der" else ( "public.pem" if k=="public_pem" else "public_ssh.pub" ) )
            with open(out_name, "wb") as fo:
                fo.write(v)
            print("wrote", out_name)
    elif args.cmd == "match":
        with open(args.priv, "rb") as f: priv = f.read()
        with open(args.cert, "rb") as f: cert = f.read()
        ok = match_private_with_certificate(priv, cert)
        print("MATCH" if ok else "NO MATCH")
    elif args.cmd == "gen":
        with open(args.priv, "rb") as f: priv = f.read()
        san_list = [s.strip() for s in args.san.split(",") if s.strip()] or None
        if args.__dict__.get("self"):
            pem = generate_selfsigned_from_priv(priv, subject_cn=args.cn, days=365, san_dns=san_list)
            out = "selfsigned.pem"
        else:
            pem = generate_csr_from_priv(priv, subject_cn=args.cn, san_dns=san_list)
            out = "request.csr"
        with open(out, "wb") as fo:
            fo.write(pem)
        print("wrote", out)
    elif args.cmd == "pem2jwk":
        raw = open(args.pem, "rb").read()
        try:
            priv = serialization.load_pem_private_key(raw, password=None)
            print(json.dumps(private_key_to_jwk_obj(priv), indent=2))
        except Exception:
            pub = load_any_public_key(raw)
            if pub is None:
                raise SystemExit("Not a valid PEM public/private key")
            print(json.dumps(public_key_to_jwk_obj(pub), indent=2))
    elif args.cmd == "web" or args.cmd is None:
        # default: start web
        host = getattr(args, "host", "127.0.0.1")
        port = getattr(args, "port", 5000)
        debug = getattr(args, "debug", False)
        app.run(host=host, port=port, debug=debug)
    else:
        p.print_help()


if __name__ == "__main__":
    cli()
