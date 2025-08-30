#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import re
import io
import json
import base64
import hashlib
from datetime import datetime, timedelta
from typing import Optional, Tuple, Dict, Any, List

from flask import Flask, render_template_string, request, send_file

from cryptography import x509
from cryptography.x509 import NameOID
from cryptography.hazmat.primitives import serialization, hashes
from cryptography.hazmat.primitives.serialization import Encoding, PrivateFormat, PublicFormat, NoEncryption, BestAvailableEncryption
from cryptography.hazmat.primitives.asymmetric import rsa, ec, ed25519
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

def analyze_bytes(raw: bytes, filename: str = "input") -> Dict[str, Any]:
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


# =========================
# Flask Web App
# =========================

app = Flask(__name__)

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
</style>
</head>
<body>
<h1>Enterprise PEM/Certificate Analyzer</h1>

<div class="card">
  <h2>۱) تحلیل کلید/سرتیفیکیت</h2>
  <form method="post" action="/analyze" enctype="multipart/form-data">
    <label>فایل PEM/Cert/SSH:</label>
    <input type="file" name="file" required>
    <button class="btn" type="submit">تحلیل</button>
  </form>
</div>

<div class="card">
  <h2>۲) ایجاد CSR / Self-Signed</h2>
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
  <h2>۳) تبدیل فرمت‌ها</h2>
  <form method="post" action="/convert" enctype="multipart/form-data">
    <label>Private Key (PEM):</label>
    <input type="file" name="priv" required>
    <label>Password برای خروجی PKCS#8 رمزدار (اختیاری):</label>
    <input type="password" name="password" placeholder="optional">
    <button class="btn" type="submit">تبدیل</button>
  </form>
</div>

<div class="card">
  <h2>۴) تطبیق Private Key و Certificate</h2>
  <form method="post" action="/match" enctype="multipart/form-data">
    <label>Private Key (PEM):</label>
    <input type="file" name="priv" required>
    <label>Certificate (PEM):</label>
    <input type="file" name="cert" required>
    <button class="btn" type="submit">بررسی تطبیق</button>
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
  <pre>{{ result.json }}</pre>
  {% if result.download_name %}
    <p><a class="btn" href="/download?path={{ result.download_path }}&name={{ result.download_name }}">دانلود خروجی</a></p>
  {% endif %}
  {% if result.report_html or result.report_md %}
    {% if result.report_html %}<p><a class="btn" href="/download?path={{ result.report_html }}&name=report.html">دانلود گزارش HTML</a></p>{% endif %}
    {% if result.report_md %}<p><a class="btn" href="/download?path={{ result.report_md }}&name=report.md">دانلود گزارش Markdown</a></p>{% endif %}
  {% endif %}
</div>
{% endif %}

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
    ts = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
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


@app.route("/", methods=["GET", "POST"])
def index():
    if request.method == "POST":
        domain = request.form.get("domain")  # ورودی از فرم
        if not domain:
            return "لطفاً دامنه وارد کنید!", 400

        # اجرای عملیات اصلی (مثلاً اسکن یا تولید گزارش)
        result = {"domain": domain, "status": "done"}

        return jsonify(result)  # برگردوندن خروجی به صورت JSON

    return render_template("index.html")


@app.route("/analyze", methods=["POST"])
def route_analyze():
    file = request.files.get("file")
    raw = file.read()
    data = analyze_bytes(raw, filename=file.filename)
    pie_div = _pie_div(data["details"].get("security"))
    html_report, md_report = _make_report_files(data)
    badge = None
    sec = data["details"].get("security")
    if sec == "Strong":
        badge = {"text": "امنیت قوی", "color": "green"}
    elif sec == "Medium":
        badge = {"text": "امنیت متوسط", "color": "orange"}
    elif sec == "Weak":
        badge = {"text": "امنیت ضعیف", "color": "red"}

    result = {
        "plot_div": pie_div,
        "json": json.dumps(data, indent=2, ensure_ascii=False),
        "badge": badge,
        "report_html": html_report,
        "report_md": md_report,
        "download_name": None,
        "download_path": None,
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
        "report_html": html_report,
        "report_md": md_report,
        "download_name": out_name,
        "download_path": path,
    }
    return render_template_string(INDEX_HTML, result=result)


@app.route("/convert", methods=["POST"])
def route_convert():
    file = request.files.get("priv")
    password = request.form.get("password") or None
    raw = file.read()
    outputs = convert_formats_from_priv(raw, passphrase=password)
    manifest = {}
    saved_paths = []
    for name, content in outputs.items():
        out_name = f"{name}.{'pem' if name.endswith('_pem') or 'public_pem' in name else 'bin'}"
        # adjust good names
        if name == "private_der": out_name = "private.der"
        if name == "public_pem":  out_name = "public.pem"
        if name == "public_ssh":  out_name = "public_ssh.pub"
        full = f"/tmp/{out_name}"
        with open(full, "wb") as f:
            f.write(content)
        manifest[name] = out_name
        saved_paths.append(full)

    res = {"status": "ok", "artifacts": manifest}
    pie_div = ""
    html_report, md_report = _make_report_files(res)

    # provide ZIP? keep it simple: suggest individual downloads in manifest via next action; here single button downloads nothing.
    result = {
        "plot_div": pie_div,
        "json": json.dumps(res, indent=2, ensure_ascii=False),
        "badge": {"text": "تبدیل انجام شد", "color": "green"},
        "report_html": html_report,
        "report_md": md_report,
        "download_name": None,
        "download_path": None,
    }
    return render_template_string(INDEX_HTML, result=result)


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

    data = {"match": bool(ok), "error": err}
    pie_div = ""
    html_report, md_report = _make_report_files(data)
    badge = {"text": "تطبیق: بله" if ok else "تطبیق: خیر", "color": "green" if ok else "red"}

    result = {
        "plot_div": pie_div,
        "json": json.dumps(data, indent=2, ensure_ascii=False),
        "badge": badge,
        "report_html": html_report,
        "report_md": md_report,
        "download_name": None,
        "download_path": None,
    }
    return render_template_string(INDEX_HTML, result=result)


@app.route("/download", methods=["GET"])
def route_download():
    path = request.args.get("path")
    name = request.args.get("name") or os.path.basename(path)
    if not path or not os.path.exists(path):
        return "file not found", 404
    return send_file(path, as_attachment=True, download_name=name)


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
