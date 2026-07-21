"""喜鹊儿一键登录与账号信息读取。

本文件是可直接运行的脚本，只保留以下链路：

1. 通过学校代码或名称查询学校服务地址；
2. 优先使用 WAP ``getLoginInfoNew`` 登录；
3. 自动尝试旧 SOAP、manager 明文及兼容签名登录兜底；
4. 登录成功后读取 ``auth/getUserInfo`` 账号资料；
5. 所有认证数据只保存在当前进程内存中。

运行时只需要安装 requests 和 pycryptodome。
不包含签到、打卡、报表等业务功能。
"""

from __future__ import annotations

import base64
import hashlib
import json
import math
import re
import secrets
import time
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, fields
from getpass import getpass
from html import unescape
from typing import Any
from urllib.parse import unquote, unquote_plus, urlparse
from xml.sax.saxutils import escape

try:
    import requests
    from Crypto.Cipher import AES, PKCS1_v1_5
    from Crypto.PublicKey import RSA
    from requests.adapters import HTTPAdapter
    from urllib3.util.retry import Retry
except ImportError as exc: 
    raise SystemExit(
        "缺少运行依赖，请先执行：python -m pip install requests pycryptodome"
    ) from exc


MANAGER_BASE_URL = "https://api.xiqueer.com/manager"
MANAGER_LOGIN_URL = f"{MANAGER_BASE_URL}/auth/login"
MANAGER_PROFILE_URL = f"{MANAGER_BASE_URL}/auth/getUserInfo"
SCHOOL_LOOKUP_URL = f"{MANAGER_BASE_URL}/wap/wapController.jsp"
DEFAULT_WAP_SERVICE_URL = "http://api.xiqueer.com/manager"
LEGACY_SOAP_URL = "http://service.kingosoft.com/android/workexpense.asmx"
USER_AGENT = "xiqueer-login-standalone/1.0"
APP_VERSION = "2.6.453"
DEVICE_NAME = "Python-Standalone"

AES_APP_KEY = b"loginkeyapp93214"
AES_APP_IV = b"12fg45gpsdfz34ab"
LEGACY_SOAP_KEY = "1pznl30029vt"
NDK_ZDY_KEY = "yt6n78"
BASE36_ALPHABET = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
NDK_BASE36_ALPHABET = "0123456789abcdefghijklmnopqrstuvwxyz"
NDK_ECHO_ALPHABET = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890"
NDK_LOGIN_FIELD_ORDER = (
    "pwdsfzm",
    "loginId",
    "sswl",
    "os",
    "xtbb",
    "appver",
    "isky",
    "zddl",
    "xxdm",
    "checktoken",
    "sjxh",
    "action",
    "sjbz",
    "pwd",
    "loginmode",
)
DEFAULT_SERVER_RSA_PUBLIC_KEY = (
    "MIGfMA0GCSqGSIb3DQEBAQUAA4GNADCBiQKBgQCas4d50ICb7CndbHiSZbxnSHKw"
    "LFPSlEYDLP6JCAI21LumZ9aQslzTYEdbUoE2PfxfEROrYJ6tgZn8wHrCwXRT1RjS"
    "84VeV3Cu8u78Kr1ZgpJj9USj-CF4jiL7RztjkleWQr4b0HGP54DSgDoqp7R9j0r"
    "-IFlEyb-FarSwqk7eAwIDAQAB"
)
DEFAULT_APP_RSA_PRIVATE_KEY = (
    "MIICdgIBADANBgkqhkiG9w0BAQEFAASCAmAwggJcAgEAAoGBAIR5Q78yidl14R1O"
    "u-EKjs0_tQg4-0APwKDDe2NJ04OMRSnYUoTJI3rv-8cZ548kvwioh6IcWp6yzTd9"
    "QQK3lpJdpko2ouVnrInUIlZAJ4l9FCq36NAGb2Rzh6zoP5s5lUugPj_ZbRuPpoyR"
    "ZLHy3SZHoIjosCvvjD7BkJm7snTHAgMBAAECgYBPKhhuHcl7BpKsbOyhoymLRlLs"
    "wwCCW-eFKsyFnQylRCHgy8EkUP6-7MLNTJGwXQk8J1pGaiNNSxSP4G4FLajwmqA"
    "p7-PUAt8aiSh578n-hSyBM9lMB77LC_-AFoTLNnbkqziu5QWyrwsOe6ekoSTf2W"
    "ko1k_j2xicCrmUmcBZQQJBALpyoXq9oRdX8in5XsrZqHOPgRevQH937rUieB0Fv"
    "EpKiV3ySbl-NxrNWd1BnHvNWhul7bgmd5rxqOc4H7nGuukCQQC15Dj1Hl8R82WX"
    "rlHK4cz2TpOA7_WLPHflSNznA5RX_q2kSOojdYW_xdb20qEbsjZ-mFv4jbeANo"
    "38t7TXZoQvAkEAtHkzH4kgvmTNrp2IiRfou3tD_PYRm5EuybyEwasEmHDPyNU3"
    "Ucr_cf0mKEpTO28J8stJcMAjdCLJWI71_rCDyQJAcxOT8Yioj1vVX5SbDOe02_"
    "Q0oDOwvsmf9UEW-VUrakynoTO8Zni5CO5rJTd3VGV40rkkHunSOdzKEiRL1qd2"
    "YwJAAy5Nl_4J2UlLa-jR6pWoasf0WNIsLbMrvCwtoO28KcSJW09UyyENL8-I7"
    "qSLhv0qV1A8lHlr_1U6308ER0wRlA"
)


class XiqueerLoginError(RuntimeError):
    """独立登录脚本基础异常。"""


class NetworkError(XiqueerLoginError):
    """网络请求异常。"""


class ProtocolError(XiqueerLoginError):
    """响应结构或加密协议异常。"""


class AuthenticationError(XiqueerLoginError):
    """所有登录链路均未建立有效会话。"""


@dataclass(slots=True)
class User:
    """登录响应及资料接口中的账号信息。"""

    user_id: str = ""
    name: str = ""
    user_type: str = ""
    uuid: str = ""
    school_code: str = ""
    school_name: str = ""
    student_number: str = ""
    gender: str = ""
    college: str = ""
    major: str = ""
    class_name: str = ""
    admission_year: str = ""
    phone: str = ""
    email: str = ""

    @classmethod
    def from_mapping(cls, data: Mapping[str, Any]) -> User:
        return cls(
            user_id=_text(data, "user_id", "userid", "userId", "uid"),
            name=_text(data, "name", "xm", "mc"),
            user_type=_text(data, "user_type", "usertype", "userType"),
            uuid=_text(data, "uuid"),
            school_code=_text(data, "school_code", "xxdm"),
            school_name=_text(data, "school_name", "xxmc"),
            student_number=_text(data, "student_number", "xh", "xsxh"),
            gender=_text(data, "gender", "xb"),
            college=_text(data, "college", "yx"),
            major=_text(data, "major", "zy"),
            class_name=_text(data, "class_name", "ssbj"),
            admission_year=_text(data, "admission_year", "rxnj"),
            phone=_text(data, "phone", "lxrdh", "pho"),
            email=_text(data, "email", "lxryj"),
        )

    def to_dict(self) -> dict[str, str]:
        """仅输出账号资料"""

        return {
            "userid": self.user_id,
            "xm": self.name,
            "usertype": self.user_type,
            "uuid": self.uuid,
            "xxdm": self.school_code,
            "xxmc": self.school_name,
            "xh": self.student_number,
            "xb": self.gender,
            "yx": self.college,
            "zy": self.major,
            "ssbj": self.class_name,
            "rxnj": self.admission_year,
            "lxrdh": self.phone,
            "lxryj": self.email,
        }


@dataclass(slots=True)
class SessionState:
    """只存在于当前进程内存中的登录状态。"""

    user: User
    token: str = ""
    jwt: str = ""
    service_url: str = ""
    metadata: dict[str, Any] | None = None

    @property
    def authenticated(self) -> bool:
        return bool(self.token or self.jwt) and bool(self.user.user_id)

    def auth_headers(self) -> dict[str, str]:
        headers: dict[str, str] = {}
        if self.jwt:
            headers["Authorization_kingo"] = self.jwt
        if self.token:
            headers["authorization"] = f"bearer {self.token}"
        return headers

    def common_parameters(self) -> dict[str, str]:
        return {
            "userId": self.user.user_id,
            "usertype": self.user.user_type,
        }


@dataclass(frozen=True, slots=True)
class LoginResult:
    """成功登录使用的链路及内存会话。"""

    method: str
    state: SessionState


@dataclass(frozen=True, slots=True)
class ProfileResult:
    """账号资料及其来源。"""

    profile: User
    source: str
    warning: str = ""


def _pick(data: Mapping[str, Any], *keys: str, default: Any = "") -> Any:
    for key in keys:
        value = data.get(key)
        if value is not None:
            return value
    return default


def _text(data: Mapping[str, Any], *keys: str, default: str = "") -> str:
    value = _pick(data, *keys, default=default)
    return default if value is None else str(value).strip()


def _first_mapping(value: Any, *keys: str) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        return {}
    for key in keys:
        item = value.get(key)
        if isinstance(item, Mapping):
            return dict(item)
    return {}


def _business_success(value: Any) -> bool:
    if not isinstance(value, Mapping):
        return True
    for key in ("errcode", "flag", "state", "success", "status", "code"):
        if key not in value:
            continue
        raw = value[key]
        if isinstance(raw, bool):
            return raw
        normalized = str(raw).strip().lower()
        if key in {"errcode", "code"}:
            return normalized in {"0", "200", "success", "ok"}
        if key == "flag":
            return normalized in {"0", "true", "success", "ok"}
        if key == "state":
            return normalized in {"1", "0", "true", "success", "ok"}
        return normalized in {"1", "0", "true", "success", "ok", "200"}
    return True


def _business_message(value: Any) -> str:
    if not isinstance(value, Mapping):
        return ""
    for key in ("msg", "message", "error", "errmsg", "result"):
        item = value.get(key)
        if item not in (None, "") and not isinstance(item, (Mapping, list)):
            return str(item)
    return ""


def _decode_escaped_text(text: str) -> str:
    decoded = unescape(str(text or "").strip())
    try:
        decoded = unquote_plus(decoded)
    except Exception:
        pass
    return re.sub(
        r"%u([0-9a-fA-F]{4})",
        lambda match: chr(int(match.group(1), 16)),
        decoded,
    )


def _text_has_login_failure(value: Any) -> bool:
    if value in (None, ""):
        return False
    text = _decode_escaped_text(str(value)).lower()
    markers = (
        "账号或密码错误",
        "账号密码错误",
        "帐号或密码错误",
        "帐号密码错误",
        "密码错误",
        "密码不正确",
        "账号不存在",
        "帐号不存在",
        "账户不存在",
        "用户不存在",
        "登录失败",
        "认证失败",
        "验证失败",
        "invalid password",
        "incorrect password",
        "login failed",
        "login fail",
        "not exist",
        "does not exist",
    )
    return any(marker in text for marker in markers)


def _login_payload_has_failure_marker(value: Any, *, depth: int = 0) -> bool:
    if depth > 4:
        return False
    if isinstance(value, Mapping):
        for key, item in value.items():
            lowered_key = str(key).strip().lower()
            if lowered_key in {"token", "access_token", "jwt"}:
                if str(item).strip().lower() == "error":
                    return True
            if isinstance(item, (Mapping, list, tuple)):
                if _login_payload_has_failure_marker(item, depth=depth + 1):
                    return True
            elif _text_has_login_failure(item):
                return True
        return False
    if isinstance(value, (list, tuple)):
        return any(
            _login_payload_has_failure_marker(item, depth=depth + 1)
            for item in value
        )
    return _text_has_login_failure(value)


def _valid_auth_text(value: Any) -> str:
    text = str(value or "").strip()
    if text.lower() in {"", "error", "null", "none", "false", "undefined", "nan"}:
        return ""
    return text


def _first_valid_auth_value(data: Mapping[str, Any], *keys: str) -> str:
    for key in keys:
        if key in data:
            value = _valid_auth_text(data.get(key))
            if value:
                return value
    return ""


def _normalize_login_payload(value: Any) -> dict[str, Any]:
    if isinstance(value, str):
        parsed = _loads_json_like(value)
        if parsed == value:
            return {}
        return _normalize_login_payload(parsed)
    if isinstance(value, list):
        for item in value:
            if isinstance(item, Mapping):
                return dict(item)
        return {}
    if not isinstance(value, Mapping):
        return {}
    data = dict(value)
    for key in (
        "data",
        "result",
        "resultSet",
        "person",
        "user",
        "student",
        "personMessage",
        "PersonMessage",
        "LOGINSTR",
    ):
        item = data.get(key)
        if isinstance(item, Mapping):
            merged = dict(item)
            for outer_key in ("token", "jwt", "serviceUrl", "serviceurl", "pwdStr"):
                if outer_key in data and outer_key not in merged:
                    merged[outer_key] = data[outer_key]
            return merged
        if isinstance(item, str):
            nested = _normalize_login_payload(item)
            if nested:
                for outer_key in ("token", "jwt", "serviceUrl", "serviceurl", "pwdStr"):
                    if outer_key in data and outer_key not in nested:
                        nested[outer_key] = data[outer_key]
                return nested
    return data


def _has_login_session_material(data: Mapping[str, Any]) -> bool:
    if _login_payload_has_failure_marker(data):
        return False
    return bool(
        _first_valid_auth_value(
            data,
            "token",
            "access_token",
            "jwt",
            "Authorization_kingo",
        )
    )


def _state_from_login_response(
    response: Any,
    *,
    username: str,
    service_url: str = "",
) -> SessionState:
    if not isinstance(response, Mapping):
        raise AuthenticationError("登录响应不是对象，无法提取会话")
    data = _first_mapping(
        response,
        "data",
        "result",
        "resultSet",
        "person",
        "user",
        "student",
        "personMessage",
        "PersonMessage",
    ) or dict(response)
    if _login_payload_has_failure_marker(data) or _login_payload_has_failure_marker(response):
        raise AuthenticationError(_business_message(data) or "登录响应包含失败标记")
    if not (_has_login_session_material(data) or _has_login_session_material(response)):
        raise AuthenticationError("登录响应没有返回有效会话凭据")
    user_payload = _first_mapping(
        data,
        "user",
        "person",
        "student",
        "personMessage",
        "PersonMessage",
    ) or dict(data)
    if not any(key in user_payload for key in ("userid", "userId", "uid", "user_id")):
        user_payload["userid"] = username
    user = User.from_mapping(user_payload)
    token = _first_valid_auth_value(data, "token", "access_token") or _first_valid_auth_value(
        response,
        "token",
        "access_token",
    )
    jwt = _first_valid_auth_value(
        data,
        "jwt",
        "Authorization_kingo",
    ) or _first_valid_auth_value(response, "jwt", "Authorization_kingo")
    resolved_service_url = str(
        data.get("serviceUrl")
        or data.get("serviceurl")
        or data.get("service_url")
        or response.get("serviceUrl")
        or response.get("serviceurl")
        or service_url
        or ""
    ).rstrip("/")
    metadata = {
        str(key): value
        for key, value in response.items()
        if key not in {"data", "result", "resultSet", "person", "user", "token", "jwt"}
    }
    state = SessionState(
        user=user,
        token=token,
        jwt=jwt,
        service_url=resolved_service_url,
        metadata=metadata,
    )
    if not state.authenticated:
        raise AuthenticationError("登录结果缺少有效 token/jwt 或用户身份")
    return state


def _merge_user(primary: User, fallback: User) -> User:
    values = {
        item.name: getattr(primary, item.name) or getattr(fallback, item.name)
        for item in fields(User)
    }
    return User(**values)


def _enrich_state(
    state: SessionState,
    *,
    school_code: str = "",
    school_name: str = "",
    service_url: str = "",
) -> SessionState:
    state.user.school_code = state.user.school_code or school_code
    state.user.school_name = state.user.school_name or school_name
    state.service_url = state.service_url or service_url.rstrip("/")
    return state


def _ensure_bytes(value: str | bytes) -> bytes:
    return value if isinstance(value, bytes) else str(value).encode("utf-8")


def _pkcs7_pad(data: bytes, block_size: int = 16) -> bytes:
    padding_length = block_size - (len(data) % block_size)
    return data + bytes([padding_length]) * padding_length


def _pkcs7_unpad(data: bytes, block_size: int = 16) -> bytes:
    if not data or len(data) % block_size:
        raise ProtocolError("AES 密文长度无效")
    padding_length = data[-1]
    if padding_length < 1 or padding_length > block_size:
        raise ProtocolError("AES 填充长度无效")
    if data[-padding_length:] != bytes([padding_length]) * padding_length:
        raise ProtocolError("AES 填充内容无效")
    return data[:-padding_length]


def aes_cbc_encrypt_base64(plaintext: str | bytes) -> str:
    cipher = AES.new(AES_APP_KEY, AES.MODE_CBC, AES_APP_IV)
    encrypted = cipher.encrypt(_pkcs7_pad(_ensure_bytes(plaintext)))
    return base64.b64encode(encrypted).decode("ascii")


def aes_cbc_decrypt_base64(ciphertext: str | bytes) -> str:
    raw = base64.b64decode(_ensure_bytes(ciphertext))
    cipher = AES.new(AES_APP_KEY, AES.MODE_CBC, AES_APP_IV)
    return _pkcs7_unpad(cipher.decrypt(raw)).decode("utf-8")


def md5_hex(value: str | bytes) -> str:
    return hashlib.md5(_ensure_bytes(value)).hexdigest()


def base64_urlsafe(value: str | bytes) -> str:
    return base64.urlsafe_b64encode(_ensure_bytes(value)).decode("ascii").rstrip("=")


def _base36_encode(value: int, alphabet: str) -> str:
    number = int(value)
    if number < 0:
        return "-" + _base36_encode(-number, alphabet)
    if number == 0:
        return "0"
    output = ""
    while number > 0:
        number, index = divmod(number, 36)
        output = alphabet[index] + output
    return output


def ndk_encrypt_zdy(raw: str, *, key: str = NDK_ZDY_KEY) -> str:
    """复刻 APK NDKTools ``zdy`` 参数编码。"""

    if not raw or not key:
        return raw
    raw_text = str(raw)
    key_text = str(key)
    key_length = len(key_text)
    raw_length = len(raw_text)
    rows = math.ceil(raw_length / key_length)
    offset = (((raw_length + 2) // 3) * 6) % key_length
    digits: list[str] = []
    for row in range(rows):
        for column in range(1, key_length + 1):
            index = row * key_length + column
            if index > raw_length:
                break
            value = ord(raw_text[index - 1]) + ord(key_text[column - 1]) + offset
            digits.append(("000" + str(value))[-3:])
            if index == raw_length:
                break
    numeric = "".join(digits)
    chunks = [
        ("000000" + _base36_encode(int(numeric[start : start + 9]), NDK_BASE36_ALPHABET))[-6:]
        for start in range(0, len(numeric), 9)
    ]
    return "".join(chunks)


def ndk_param2(raw: str) -> str:
    if not raw:
        return ""
    digest = md5_hex(raw)
    filtered = "".join(
        character
        for index, character in enumerate(digest)
        if index not in {3, 10, 17, 25}
    )
    return md5_hex(filtered)


def ndk_form_string(
    payload: Mapping[str, Any],
    *,
    field_order: Sequence[str] | None = None,
) -> str:
    items = {
        str(key): "" if value is None else str(value)
        for key, value in payload.items()
    }
    ordered_keys: list[str] = []
    if field_order:
        ordered_keys.extend(key for key in field_order if key in items)
    ordered_keys.extend(key for key in items if key not in ordered_keys)
    return "&".join(f"{key}={items[key]}" for key in ordered_keys)


def _normalize_base64(value: str) -> str:
    text = str(value or "").strip().replace("-", "+").replace("_", "/")
    return text + "=" * ((-len(text)) % 4)


def _rsa_public_encrypt_base64(data: str, public_key_base64: str) -> str:
    try:
        key = RSA.import_key(base64.b64decode(_normalize_base64(public_key_base64)))
        cipher = PKCS1_v1_5.new(key)
        block_size = key.size_in_bytes() - 11
        raw = _ensure_bytes(data)
        encrypted = b"".join(
            cipher.encrypt(raw[start : start + block_size])
            for start in range(0, len(raw), block_size)
        )
        return base64.b64encode(encrypted).decode("ascii")
    except Exception as exc:
        raise ProtocolError("RSA 公钥加密失败") from exc


def _rsa_private_encrypt_base64(data: str, private_key_base64: str) -> str:
    try:
        key = RSA.import_key(base64.b64decode(_normalize_base64(private_key_base64)))
        if not key.has_private():
            raise ValueError("不是 RSA 私钥")
        size = key.size_in_bytes()
        raw = _ensure_bytes(data)
        chunks: list[bytes] = []
        for start in range(0, len(raw), size - 11):
            chunk = raw[start : start + size - 11]
            padding = b"\xff" * (size - len(chunk) - 3)
            block = b"\x00\x01" + padding + b"\x00" + chunk
            chunks.append(
                pow(int.from_bytes(block, "big"), key.d, key.n).to_bytes(size, "big")
            )
        return base64.b64encode(b"".join(chunks)).decode("ascii")
    except Exception as exc:
        raise ProtocolError("RSA 私钥签名包装失败") from exc


def ndk_signature_fields(
    param_string: str,
    *,
    timestamp: str | None = None,
    echo: str | None = None,
) -> dict[str, str]:
    param = ndk_encrypt_zdy(param_string)
    timestamp_text = (timestamp or str(int(time.time() * 1000)))[:10]
    nonce = echo or "".join(secrets.choice(NDK_ECHO_ALPHABET) for _ in range(16))
    encrypted_key = _rsa_public_encrypt_base64(
        NDK_ZDY_KEY,
        DEFAULT_SERVER_RSA_PUBLIC_KEY,
    )
    sign_source = f"param={param}&param2=&timestamp={timestamp_text}&echo={nonce}"
    signature = _rsa_private_encrypt_base64(
        md5_hex(sign_source + encrypted_key),
        DEFAULT_APP_RSA_PRIVATE_KEY,
    )
    return {
        "param": param,
        "param2": ndk_param2(param_string),
        "timestamp": timestamp_text,
        "echo": nonce,
        "encrptSecretKey": encrypted_key,
        "xqerSign": signature,
    }


def native_signed_body(
    payload: Mapping[str, Any],
    *,
    preserve_wap_route: bool = False,
) -> dict[str, Any]:
    is_login_payload = {"loginId", "pwd"}.issubset({str(key) for key in payload})
    raw = ndk_form_string(
        payload,
        field_order=NDK_LOGIN_FIELD_ORDER if is_login_payload else None,
    )
    body: dict[str, Any] = ndk_signature_fields(raw)
    app_version = str(payload.get("appver") or APP_VERSION)
    body.update(
        {
            "appsjxh": str(
                payload.get("appsjxh")
                or payload.get("sjxh")
                or DEVICE_NAME
            ),
            "appinfo": str(payload.get("appinfo") or f"android{app_version}"),
            "token": str(payload.get("token") or "00000"),
        }
    )
    if preserve_wap_route:
        for key in (
            "action",
            "xxdm",
            "xxmc",
            "schoolCode",
            "schoolName",
            "appver",
        ):
            if key in payload:
                body[key] = payload[key]
    return body


def legacy_soap_param(raw: str, *, key: str = LEGACY_SOAP_KEY) -> str:
    if not raw or not key:
        return raw
    key_length = len(key)
    raw_length = len(raw)
    rows = (raw_length + key_length - 1) // key_length
    offset = (((raw_length + 2) // 3) * 6) % key_length
    digits: list[str] = []
    for row in range(rows):
        for column in range(1, key_length + 1):
            index = row * key_length + column
            if index > raw_length:
                break
            code = ord(raw[index - 1]) + ord(key[column - 1]) + offset
            digits.append(("000" + str(code))[-3:])
            if index == raw_length:
                break
    numeric = "".join(digits)
    return "".join(
        (
            "000000"
            + _base36_encode(
                int(numeric[start : start + 9]),
                BASE36_ALPHABET,
            )
        )[-6:]
        for start in range(0, len(numeric), 9)
    )


def legacy_soap_param2_variants(raw: str) -> dict[str, str]:
    digest = md5_hex(raw)
    selected = digest[2] + digest[9] + digest[16] + digest[24]
    exclude_java8 = "".join(
        character
        for index, character in enumerate(digest)
        if index not in {3, 10, 17, 25}
    )
    exclude_android = "".join(
        character
        for index, character in enumerate(digest)
        if index not in {2, 9, 16, 24}
    )
    return {
        "selected": md5_hex(selected),
        "exclude_java8": md5_hex(exclude_java8),
        "exclude_android_legacy": md5_hex(exclude_android),
        "raw_md5": digest,
    }


def _json_candidates(text: str) -> list[str]:
    stripped = text.strip()
    candidates: list[str] = []
    if stripped.startswith(("{", "[")):
        candidates.append(stripped)
    for opener, closer in (("{", "}"), ("[", "]")):
        start = stripped.find(opener)
        end = stripped.rfind(closer)
        if start != -1 and end > start:
            candidate = stripped[start : end + 1]
            if candidate not in candidates:
                candidates.append(candidate)
    return candidates


def _loads_json_like(value: Any) -> Any:
    if isinstance(value, (Mapping, list)):
        return value
    if isinstance(value, bytes):
        text = value.decode("utf-8", errors="replace")
    else:
        text = str(value or "")
    text = unescape(text.strip())
    if not text:
        return ""
    text_variants = [text, unquote(text), unquote_plus(text)]
    for variant in text_variants:
        for candidate in _json_candidates(variant):
            try:
                return json.loads(candidate)
            except json.JSONDecodeError:
                continue
    for variant in text_variants:
        try:
            decrypted = aes_cbc_decrypt_base64(variant).strip()
        except Exception:
            continue
        for candidate in _json_candidates(decrypted):
            try:
                return json.loads(candidate)
            except json.JSONDecodeError:
                continue
        if decrypted:
            return decrypted
    return text


def _response_rows(value: Any, *, depth: int = 0) -> list[dict[str, Any]]:
    if depth > 5:
        return []
    parsed = _loads_json_like(value)
    if isinstance(parsed, list):
        rows: list[dict[str, Any]] = []
        for item in parsed:
            if isinstance(item, Mapping):
                rows.append(dict(item))
            elif isinstance(item, str):
                rows.extend(_response_rows(item, depth=depth + 1))
        return rows
    if not isinstance(parsed, Mapping):
        return []
    if _service_url_from_row(parsed):
        return [dict(parsed)]
    for key in (
        "RegisterData",
        "registerData",
        "rows",
        "list",
        "data",
        "resultSet",
        "result",
        "schools",
        "schoolList",
        "agentList",
        "items",
    ):
        if key in parsed:
            rows = _response_rows(parsed.get(key), depth=depth + 1)
            if rows:
                return rows
    for item in parsed.values():
        if isinstance(item, (Mapping, list, str)):
            rows = _response_rows(item, depth=depth + 1)
            if rows:
                return rows
    return []


def _row_text(row: Mapping[str, Any], *keys: str) -> str:
    lowered = {str(key).lower(): value for key, value in row.items()}
    for key in keys:
        value = row.get(key)
        if value in (None, ""):
            value = lowered.get(key.lower())
        if value not in (None, ""):
            return str(value).strip()
    return ""


def _school_code_from_row(row: Mapping[str, Any]) -> str:
    return _row_text(row, "xxdm", "schoolCode", "school_code", "code", "agentCode")


def _school_name_from_row(row: Mapping[str, Any]) -> str:
    return _row_text(row, "xxmc", "schoolName", "school_name", "name", "agentName")


def _service_url_from_row(row: Mapping[str, Any]) -> str:
    return _row_text(
        row,
        "serviceUrl",
        "serviceurl",
        "service_url",
        "serverUrl",
        "wapUrl",
        "agentUrl",
        "url",
        "fwurl",
        "fwqdz",
    )


def _normalize_school_inputs(
    school_code: str = "",
    school_name: str = "",
) -> tuple[str, str]:
    code = str(school_code or "").strip()
    name = str(school_name or "").strip()
    if code and not name and not code.isdigit():
        return "", code
    return code, name


def _normalize_service_url(value: Any) -> str:
    text = str(value or "").strip().rstrip("/")
    if not text:
        return ""
    if not text.lower().startswith(("http://", "https://")):
        if "." not in text or text.startswith("/"):
            return ""
        text = "https://" + text
    parsed = urlparse(text)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        return ""
    return text.rstrip("/")


def _wap_controller_url(service_url: str) -> str:
    base_url = _normalize_service_url(service_url)
    if not base_url:
        raise ProtocolError("学校服务地址 serviceUrl 无效")
    lowered = base_url.lower()
    if lowered.endswith("/wap/wapcontroller.jsp"):
        return base_url
    if lowered.endswith("/wap"):
        return base_url + "/wapController.jsp"
    return base_url + "/wap/wapController.jsp"


def _soap_envelope(fields_value: Mapping[str, str]) -> str:
    body = "".join(
        f"<{name}>{escape(value)}</{name}>"
        for name, value in fields_value.items()
    )
    return (
        '<?xml version="1.0" encoding="utf-8"?>'
        '<soap:Envelope xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" '
        'xmlns:xsd="http://www.w3.org/2001/XMLSchema" '
        'xmlns:soap="http://schemas.xmlsoap.org/soap/envelope/">'
        '<soap:Body><login xmlns="http://e.kingosoft.com/">'
        f"{body}</login></soap:Body></soap:Envelope>"
    )


def _parse_soap_result(text: str) -> Any:
    match = re.search(
        r"<(?:\w+:)?loginResult(?:\s[^>]*)?>(.*?)</(?:\w+:)?loginResult>",
        text,
        re.S | re.I,
    )
    if match:
        result = unescape(match.group(1).strip())
    elif re.search(r"<(?:\w+:)?loginResult(?:\s[^>]*)?\s/>", text, re.I):
        result = ""
    else:
        result = unescape(text.strip())
    return _loads_json_like(result)


def _redact_text(value: Any, *, limit: int = 180) -> str:
    text = str(value or "").replace("\r", " ").replace("\n", " ")
    pattern = (
        r"(?i)(password|passwd|pwd|token|jwt|authorization|cookie|"
        r"param2?|xqersign|encrptsecretkey|loginid|userid)\s*[:=]\s*[^\s,&<>]+"
    )
    text = re.sub(pattern, lambda match: match.group(1) + "=<redacted>", text)
    return text[:limit] + "..." if len(text) > limit else text


class HttpClient:
    """当前运行周期内使用的短生命周期 HTTP 会话。"""

    def __init__(self, session: requests.Session | None = None) -> None:
        self.session = session or requests.Session()
        self.timeout = (10.0, 30.0)
        self.session.headers.update(
            {
                "User-Agent": USER_AGENT,
                "Accept": "application/json, text/plain, */*",
            }
        )
        retry = Retry(
            total=3,
            connect=3,
            read=2,
            backoff_factor=0.4,
            status_forcelist=(429, 500, 502, 503, 504),
            allowed_methods=frozenset(("GET", "HEAD", "OPTIONS")),
        )
        adapter = HTTPAdapter(max_retries=retry, pool_connections=8, pool_maxsize=8)
        self.session.mount("http://", adapter)
        self.session.mount("https://", adapter)

    def request(self, method: str, url: str, **kwargs: Any) -> requests.Response:
        kwargs.setdefault("timeout", self.timeout)
        try:
            response = self.session.request(method.upper(), url, **kwargs)
        except requests.RequestException as exc:
            raise NetworkError(f"请求失败：{method.upper()} {url}：{exc}") from exc
        if response.status_code >= 400:
            raise NetworkError(f"接口返回 HTTP {response.status_code}：{method.upper()} {url}")
        return response

    @staticmethod
    def parse_response(response: requests.Response, *, expected_json: bool) -> Any:
        text = response.text
        if not text:
            return {}
        try:
            return response.json()
        except (ValueError, json.JSONDecodeError):
            parsed = _loads_json_like(text)
            if not isinstance(parsed, str) or parsed != text.strip():
                return parsed
            if expected_json:
                raise ProtocolError("接口未返回可识别的 JSON")
            return text

    def close(self) -> None:
        self.session.close()

    def __enter__(self) -> HttpClient:
        return self

    def __exit__(self, exc_type, exc, traceback) -> None:
        self.close()


class AuthService:
    """学校发现及多链路登录编排。"""

    def __init__(self, http: HttpClient) -> None:
        self.http = http

    def lookup_school_candidates(
        self,
        school_code: str = "",
        school_name: str = "",
    ) -> list[dict[str, Any]]:
        school_code, school_name = _normalize_school_inputs(school_code, school_name)
        params: dict[str, str] = {
            "action": "getAgent",
            "appver": APP_VERSION,
            "xxmc": school_name,
        }
        if school_code:
            params["xxdm"] = school_code
        response = self.http.request("GET", SCHOOL_LOOKUP_URL, params=params)
        parsed = self.http.parse_response(response, expected_json=False)
        rows = _response_rows(parsed)
        if school_code:
            matches = [row for row in rows if _school_code_from_row(row) == school_code]
            if matches:
                return matches
        if school_name:
            target = school_name.casefold()
            exact = [
                row
                for row in rows
                if _school_name_from_row(row).casefold() == target
            ]
            if exact:
                return exact
            return [
                row
                for row in rows
                if target in _school_name_from_row(row).casefold()
                or target in _row_text(row, "pinyin", "py", "spell").casefold()
            ]
        return rows

    def candidate_service_targets(
        self,
        school_code: str = "",
        school_name: str = "",
        *,
        service_url: str = "",
    ) -> list[dict[str, str]]:
        school_code, school_name = _normalize_school_inputs(school_code, school_name)
        targets: list[dict[str, str]] = []
        seen: set[tuple[str, str]] = set()

        def add(raw_url: Any, *, code: str = "", name: str = "", source: str) -> None:
            normalized = _normalize_service_url(raw_url)
            if not normalized:
                return
            target_code, target_name = _normalize_school_inputs(
                code or school_code,
                name or school_name,
            )
            key = (normalized, target_code)
            if key in seen:
                return
            seen.add(key)
            targets.append(
                {
                    "service_url": normalized,
                    "school_code": target_code,
                    "school_name": target_name,
                    "source": source,
                }
            )

        add(service_url, source="input")
        add(DEFAULT_WAP_SERVICE_URL, source="default")
        if school_code or school_name:
            try:
                rows = self.lookup_school_candidates(school_code, school_name)
            except XiqueerLoginError:
                if targets:
                    return targets
                raise
            for row in rows:
                add(
                    _service_url_from_row(row),
                    code=_school_code_from_row(row),
                    name=_school_name_from_row(row),
                    source="school_lookup",
                )
        return targets

    @staticmethod
    def wap_login_payload_variants(
        username: str,
        password: str,
        *,
        school_code: str,
    ) -> list[tuple[str, dict[str, Any]]]:
        base_payload: dict[str, Any] = {
            "pwdsfzm": "1",
            "xxdm": school_code,
            "isky": "1",
            "sjbz": "",
            "sswl": "",
            "sjxh": DEVICE_NAME,
            "os": "android",
            "xtbb": "13",
            "appver": APP_VERSION,
            "checktoken": "true",
            "action": "getLoginInfoNew",
            "zddl": "1",
        }
        identities = (
            ("loginId_plain", {"loginId": username}),
            ("loginId_b64", {"loginId": base64_urlsafe(username)}),
            ("userId_plain", {"loginId": username, "userId": username}),
            ("xqzh_plain", {"loginId": username, "xqzh": username}),
            ("loginId_md5", {"loginId": md5_hex(username)}),
        )
        passwords = (
            ("pwd_plain", {"pwd": password}),
            ("pwd_password_plain", {"pwd": password, "password": password}),
            (
                "pwd_aes_pwdsfzm",
                {"pwd": aes_cbc_encrypt_base64(password), "pwdsfzm": "1"},
            ),
        )
        variants: list[tuple[str, dict[str, Any]]] = []
        seen: set[tuple[tuple[str, str], ...]] = set()
        for login_mode in ("0", "1"):
            for identity_name, identity in identities:
                for password_name, password_fields in passwords:
                    payload = dict(base_payload)
                    payload["loginmode"] = login_mode
                    payload.update(identity)
                    payload.update(password_fields)
                    fingerprint = tuple(
                        sorted((key, str(value)) for key, value in payload.items())
                    )
                    if fingerprint in seen:
                        continue
                    seen.add(fingerprint)
                    variants.append(
                        (
                            f"mode{login_mode}_{identity_name}_{password_name}",
                            payload,
                        )
                    )
        return variants

    def wap_login(
        self,
        username: str,
        password: str,
        *,
        school_code: str,
        school_name: str,
        service_url: str,
    ) -> SessionState:
        raw_variants = self.wap_login_payload_variants(
            username,
            password,
            school_code=school_code,
        )
        messages: list[str] = []
        url = _wap_controller_url(service_url)
        headers = {"Content-Type": "application/x-www-form-urlencoded; charset=UTF-8"}
        for encrypted in (True, False):
            for raw_name, raw_payload in raw_variants:
                name = ("encrypted_" if encrypted else "") + raw_name
                try:
                    payload = (
                        native_signed_body(raw_payload, preserve_wap_route=True)
                        if encrypted
                        else raw_payload
                    )
                    response = self.http.request(
                        "POST",
                        url,
                        data=payload,
                        headers=headers,
                    )
                    parsed = self.http.parse_response(response, expected_json=False)
                except XiqueerLoginError as exc:
                    messages.append(f"{name}: {_redact_text(exc)}")
                    continue
                normalized = _normalize_login_payload(parsed)
                if (
                    _business_success(parsed)
                    and not _login_payload_has_failure_marker(parsed)
                    and normalized
                    and _has_login_session_material(normalized)
                ):
                    state = _state_from_login_response(
                        normalized,
                        username=username,
                        service_url=service_url,
                    )
                    return _enrich_state(
                        state,
                        school_code=school_code,
                        school_name=school_name,
                        service_url=service_url,
                    )
                message = (
                    _business_message(parsed)
                    or _redact_text(parsed, limit=100)
                    or "空响应"
                )
                messages.append(f"{name}: {message}")
        detail = "；".join(messages[:6])
        raise AuthenticationError(f"WAP 登录失败：{detail or '没有可用响应'}")

    def legacy_soap_login(
        self,
        username: str,
        password: str,
    ) -> SessionState:
        messages: list[str] = []
        payload_variants = (
            ("password_userId", f"password={password}&userId={username}"),
            ("userId_password", f"userId={username}&password={password}"),
        )
        headers = {
            "Content-Type": "text/xml; charset=utf-8",
            "SOAPAction": "http://e.kingosoft.com/login",
        }
        for variant_name, raw in payload_variants:
            for mode, param2 in legacy_soap_param2_variants(raw).items():
                request_body = _soap_envelope(
                    {
                        "param": legacy_soap_param(raw),
                        "param2": param2,
                    }
                )
                try:
                    response = self.http.request(
                        "POST",
                        LEGACY_SOAP_URL,
                        data=request_body,
                        headers=headers,
                    )
                except XiqueerLoginError as exc:
                    messages.append(f"{variant_name}:{mode}: {_redact_text(exc)}")
                    continue
                parsed = _parse_soap_result(response.text)
                normalized = _normalize_login_payload(parsed)
                if (
                    normalized
                    and _business_success(normalized)
                    and not _login_payload_has_failure_marker(normalized)
                    and _has_login_session_material(normalized)
                ):
                    return _state_from_login_response(
                        normalized,
                        username=username,
                    )
                message = _business_message(normalized) or "loginResult 未包含有效会话"
                messages.append(f"{variant_name}:{mode}: {message}")
        detail = "；".join(messages[:6])
        raise AuthenticationError(f"旧 SOAP 登录失败：{detail or '没有可用响应'}")

    def manager_login(
        self,
        username: str,
        password: str,
        *,
        school_code: str,
        school_name: str,
        sign: bool,
    ) -> SessionState:
        payload: dict[str, Any] = {
            "userId": username,
            "password": password,
            "pwd": password,
        }
        if school_code:
            payload["xxdm"] = school_code
        request_payload = native_signed_body(payload) if sign else payload
        response = self.http.request(
            "POST",
            MANAGER_LOGIN_URL,
            data=request_payload,
            headers={"Accept": "application/json"},
        )
        parsed = self.http.parse_response(response, expected_json=True)
        if not _business_success(parsed):
            raise AuthenticationError(_business_message(parsed) or "manager 登录失败")
        state = _state_from_login_response(parsed, username=username)
        return _enrich_state(
            state,
            school_code=school_code,
            school_name=school_name,
        )

    def auto_login(
        self,
        username: str,
        password: str,
        *,
        school_code: str = "",
        school_name: str = "",
        service_url: str = "",
    ) -> LoginResult:
        school_code, school_name = _normalize_school_inputs(school_code, school_name)
        errors: list[str] = []
        try:
            targets = self.candidate_service_targets(
                school_code,
                school_name,
                service_url=service_url,
            )
        except XiqueerLoginError as exc:
            targets = []
            errors.append(f"学校服务地址解析失败：{_redact_text(exc)}")
        for target in targets:
            try:
                state = self.wap_login(
                    username,
                    password,
                    school_code=target["school_code"],
                    school_name=target["school_name"],
                    service_url=target["service_url"],
                )
                return LoginResult("wap_getLoginInfoNew", state)
            except XiqueerLoginError as exc:
                errors.append(
                    f"WAP({target['source']})：{_redact_text(exc)}"
                )
        try:
            state = self.legacy_soap_login(username, password)
            state = _enrich_state(
                state,
                school_code=school_code,
                school_name=school_name,
            )
            return LoginResult("legacy_soap", state)
        except XiqueerLoginError as exc:
            errors.append(f"旧 SOAP：{_redact_text(exc)}")
        for sign, method in ((False, "manager_plain"), (True, "manager_signed")):
            try:
                state = self.manager_login(
                    username,
                    password,
                    school_code=school_code,
                    school_name=school_name,
                    sign=sign,
                )
                return LoginResult(method, state)
            except XiqueerLoginError as exc:
                errors.append(f"{method}：{_redact_text(exc)}")
        raise AuthenticationError("自动登录失败；" + "；".join(errors))


class ProfileService:
    """读取当前账号资料，失败时明确回退到登录响应。"""

    def __init__(self, http: HttpClient) -> None:
        self.http = http

    def get_current(self, state: SessionState) -> ProfileResult:
        headers = {"Accept": "application/json", **state.auth_headers()}
        try:
            response = self.http.request(
                "GET",
                MANAGER_PROFILE_URL,
                params=state.common_parameters(),
                headers=headers,
            )
            parsed = self.http.parse_response(response, expected_json=True)
            if not _business_success(parsed):
                raise ProtocolError(_business_message(parsed) or "获取个人信息失败")
            data = _first_mapping(
                parsed,
                "data",
                "result",
                "resultSet",
                "user",
                "person",
            ) or (dict(parsed) if isinstance(parsed, Mapping) else {})
            profile = User.from_mapping(data)
            profile = _merge_user(profile, state.user)
            return ProfileResult(profile, "auth/getUserInfo")
        except XiqueerLoginError as exc:
            return ProfileResult(
                state.user,
                "login_response",
                f"资料接口读取失败，已使用登录响应中的资料：{_redact_text(exc)}",
            )


class XiqueerLoginClient:
    """独立脚本门面，只暴露登录与资料读取。"""

    def __init__(self, session: requests.Session | None = None) -> None:
        self.http = HttpClient(session)
        self.auth = AuthService(self.http)
        self.profile = ProfileService(self.http)

    def login_and_get_profile(
        self,
        username: str,
        password: str,
        *,
        school_code: str = "",
        school_name: str = "",
        service_url: str = "",
    ) -> tuple[LoginResult, ProfileResult]:
        login = self.auth.auto_login(
            username,
            password,
            school_code=school_code,
            school_name=school_name,
            service_url=service_url,
        )
        return login, self.profile.get_current(login.state)

    def close(self) -> None:
        self.http.close()

    def __enter__(self) -> XiqueerLoginClient:
        return self

    def __exit__(self, exc_type, exc, traceback) -> None:
        self.close()


class InteractiveLoginApp:
    
    def run(self) -> None:
        print("喜鹊儿一键登录与账号信息读取")
        print("认证信息仅保存在当前进程内存中，退出后自动丢弃。")
        while True:
            print("\n1. 账号密码登录并获取资料")
            print("0. 退出")
            try:
                choice = input("请选择：").strip()
                if choice == "0":
                    print("已退出。")
                    return
                if choice != "1":
                    print("请输入 1 或 0。")
                    continue
                self._login_flow()
            except KeyboardInterrupt:
                print("\n已取消。")
                return
            except XiqueerLoginError as exc:
                print(f"操作失败：{exc}")
            except Exception as exc:
                print(f"操作失败：{type(exc).__name__}：{exc}")

    @staticmethod
    def _login_flow() -> None:
        username = input("账号：").strip()
        if not username:
            print("账号不能为空。")
            return
        password = getpass("密码：")
        if not password:
            print("密码不能为空。")
            return
        school_identifier = input("学校代码/学校名称（可空）：").strip()
        service_url = input("学校服务地址 serviceUrl（可空）：").strip()
        school_code, school_name = _normalize_school_inputs(school_identifier, "")
        print("正在登录并读取账号资料...")
        with XiqueerLoginClient() as client:
            login, profile = client.login_and_get_profile(
                username,
                password,
                school_code=school_code,
                school_name=school_name,
                service_url=service_url,
            )
        if profile.warning:
            print(f"提示：{profile.warning}")
        result = {
            "login_method": login.method,
            "profile_source": profile.source,
            "service_url": login.state.service_url,
            "profile": profile.profile.to_dict(),
        }
        print("\n登录成功，当前账号信息如下：")
        print(json.dumps(result, ensure_ascii=False, indent=2))


def main() -> int:
    InteractiveLoginApp().run()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
