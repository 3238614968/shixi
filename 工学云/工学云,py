"""工学云一键登录

本文件是可直接运行的独立脚本，只保留以下链路：

1. 自动获取并识别 blockPuzzle 滑块验证码；
2. 通过 ``session/user/v6/login`` 完成账号登录；
3. 登录成功后读取 ``practice/plan/v3/getPlanByStu`` 实习计划；
4. 所有认证数据只保存在当前进程内存中。

运行时需要安装 requests、pycryptodome、numpy 和 opencv-python。
不包含签到、打卡、报表等业务功能。


@author: xiaohai
@date: 2026-07-24
@license: MIT
"""

from __future__ import annotations

import base64
import hashlib
import json
import random
import re
import struct
import time
import uuid
from collections.abc import Mapping
from dataclasses import dataclass, fields
from getpass import getpass
from typing import Any

try:
    import cv2
    import numpy as np
    import requests
    from Crypto.Cipher import AES
    from Crypto.Util.Padding import pad, unpad
    from requests.adapters import HTTPAdapter
    from urllib3.util.retry import Retry
except ImportError as exc:  # pragma: no cover - 仅在缺少运行依赖时触发
    raise SystemExit(
        "缺少运行依赖，请先执行：python -m pip install requests pycryptodome numpy opencv-python"
    ) from exc


# 工学云 API 基址
BASE_URL = "https://api.moguding.net:9000/"

APP_VERSIONS = (
    "5.32.6",
    "5.31.0",
    "5.30.2",
    "5.29.1",
    "5.28.4",
    "5.27.0",
)

USER_AGENTS = (
    # 小米
    "Mozilla/5.0 (Linux; Android 13; Mi 11 Ultra Build/TKQ1.220829.002; wv) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/114.0.5735.131 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 14; 23116PN5BC Build/U1CE34; wv) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/120.0.6099.144 Mobile Safari/537.36",
    # 华为
    "Mozilla/5.0 (Linux; Android 12; MATE-40-Pro Build/HUAWEIMate40Pro; wv) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/99.0.4844.88 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 14; ALN-AL00 Build/HUAWEIALN-AL00; wv) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/121.0.6167.178 Mobile Safari/537.36",
    # OPPO
    "Mozilla/5.0 (Linux; Android 13; PFEM10 Build/TP1A.220905.001; wv) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/111.0.5563.116 Mobile Safari/537.36",
    # vivo
    "Mozilla/5.0 (Linux; Android 13; V2227A Build/TP1A.220624.014; wv) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/116.0.5845.192 Mobile Safari/537.36",
    # 三星
    "Mozilla/5.0 (Linux; Android 14; SM-S9080 Build/UP1A.231005.007; wv) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/121.0.6167.178 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 13; SM-G991B Build/TP1A.220624.014; wv) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/112.0.5615.136 Mobile Safari/537.36",
    # 一加
    "Mozilla/5.0 (Linux; Android 14; NE2210 Build/U1CE34; wv) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/122.0.6261.119 Mobile Safari/537.36",
)

APP_VERSION = random.choice(APP_VERSIONS)
USER_AGENT = random.choice(USER_AGENTS)

DEVICE_NAME = "android"

DEFAULT_HEADERS = {
    "user-agent": USER_AGENT,
    "content-type": "application/json; charset=utf-8",
    "accept-encoding": "gzip",
    "host": "api.moguding.net:9000",
}

# AES/ECB/PKCS5 业务加密参数
DEFAULT_AES_KEY = b"23DbtQHR2UMbH6mJ"
SIGN_SALT = "3478cbbc33f84bd00d75d7dfa69e0daa"

# 接口路径
LOGIN_PATH = "session/user/v6/login"
CAPTCHA_GET_PATH = "session/captcha/v1/get"
CAPTCHA_CHECK_PATH = "session/captcha/v1/check"
PLAN_PATH = "practice/plan/v3/getPlanByStu"

# 业务返回码
CODE_SUCCESS = 200
CODE_CAPTCHA_RETRY = 6111


class GongxueyunLoginError(RuntimeError):
    """独立登录脚本基础异常。"""


class NetworkError(GongxueyunLoginError):
    """网络请求异常。"""


class ProtocolError(GongxueyunLoginError):
    """响应结构或加密协议异常。"""


class CaptchaError(GongxueyunLoginError):
    """滑块验证码识别或校验失败。"""


class AuthenticationError(GongxueyunLoginError):
    """登录链路未能建立有效会话。"""


@dataclass(slots=True)
class User:
    """登录响应及实习计划接口中的账号信息。"""

    user_id: str = ""
    username: str = ""
    name: str = ""
    user_type: str = ""
    role_key: str = ""
    phone: str = ""
    class_name: str = ""
    college: str = ""
    major: str = ""
    school_id: str = ""
    student_number: str = ""
    student_id: str = ""
    head_image: str = ""
    token: str = ""
    expired_time: str = ""

    @classmethod
    def from_mapping(cls, data: Mapping[str, Any]) -> User:
        return cls(
            user_id=_text(data, "userId", "user_id", "uid"),
            username=_text(data, "username", "loginName"),
            name=_text(data, "name", "nickName", "nickname"),
            user_type=_text(data, "userType", "user_type"),
            role_key=_text(data, "roleKey", "role_key"),
            phone=_text(data, "phone"),
            class_name=_text(data, "className", "class_name"),
            college=_text(data, "depName", "college"),
            major=_text(data, "majorName", "major"),
            school_id=_text(data, "schoolId", "school_id"),
            student_number=_text(data, "studentNumber", "student_number"),
            student_id=_text(data, "studentId", "student_id"),
            head_image=_text(data, "headImg", "head_image"),
            token=_text(data, "token"),
            expired_time=_text(data, "expiredTime", "expired_time"),
        )

    def to_dict(self) -> dict[str, str]:
        """仅输出账号资料。"""

        return {
            "userId": self.user_id,
            "username": self.username,
            "name": self.name,
            "userType": self.user_type,
            "roleKey": self.role_key,
            "phone": self.phone,
            "className": self.class_name,
            "depName": self.college,
            "majorName": self.major,
            "schoolId": self.school_id,
            "studentNumber": self.student_number,
            "studentId": self.student_id,
            "headImg": self.head_image,
            "token": self.token,
            "expiredTime": self.expired_time,
        }


@dataclass(slots=True)
class SessionState:
    """只存在于当前进程内存中的登录状态。"""

    user: User
    token: str = ""
    expired_time: str = ""
    metadata: dict[str, Any] | None = None

    @property
    def authenticated(self) -> bool:
        return bool(self.token) and bool(self.user.user_id)

    def auth_headers(self) -> dict[str, str]:
        headers = dict(DEFAULT_HEADERS)
        if self.token:
            headers["authorization"] = self.token
        if self.user.user_id:
            headers["userid"] = self.user.user_id
        if self.user.role_key:
            headers["rolekey"] = self.user.role_key
        return headers


@dataclass(frozen=True, slots=True)
class LoginResult:
    """成功登录使用的链路及内存会话。"""

    method: str
    state: SessionState


@dataclass(frozen=True, slots=True)
class ProfileResult:
    """账号资料及其实习计划来源。"""

    profile: User
    plan_info: dict[str, Any]
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
    if value is None:
        return default
    text = str(value).strip()
    if text.lower() in {"null", "undefined"}:
        return default
    return text


def _first_mapping(value: Any, *keys: str) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        return {}
    for key in keys:
        item = value.get(key)
        if isinstance(item, Mapping):
            return dict(item)
    return {}


def _business_success(value: Any) -> bool:
    """工学云业务响应成功标志：``code == 200``。"""

    if not isinstance(value, Mapping):
        return True
    code = value.get("code")
    if code is None:
        return True
    return str(code) == str(CODE_SUCCESS)


def _business_message(value: Any) -> str:
    if not isinstance(value, Mapping):
        return ""
    for key in ("msg", "message", "errmsg"):
        item = value.get(key)
        if item not in (None, "") and not isinstance(item, (Mapping, list)):
            return str(item)
    return ""


def _ensure_bytes(value: str | bytes) -> bytes:
    return value if isinstance(value, bytes) else str(value).encode("utf-8")


def _coerce_key(key: str | bytes) -> bytes:
    return key if isinstance(key, bytes) else str(key).encode("utf-8")


def aes_encrypt(
    plaintext: str | bytes,
    *,
    key: str | bytes = DEFAULT_AES_KEY,
    out_format: str = "hex",
) -> str:
   
    cipher = AES.new(_coerce_key(key), AES.MODE_ECB)
    encrypted = cipher.encrypt(pad(_ensure_bytes(plaintext), AES.block_size))
    if out_format == "b64":
        return base64.b64encode(encrypted).decode("ascii")
    return encrypted.hex()


def aes_decrypt(
    ciphertext: str,
    *,
    key: str | bytes = DEFAULT_AES_KEY,
    out_format: str = "hex",
) -> str:
  
    cipher = AES.new(_coerce_key(key), AES.MODE_ECB)
    if out_format == "b64":
        raw = base64.b64decode(_ensure_bytes(ciphertext))
    else:
        raw = bytes.fromhex(str(ciphertext).strip())
    return unpad(cipher.decrypt(raw), AES.block_size).decode("utf-8")


def create_sign(*args: Any) -> str:
    """参数顺序拼接并追加固定盐值后取 MD5。"""

    parts: list[str] = []
    for index, item in enumerate(args):
        if item is None:
            raise ValueError(f"签名参数缺失: index={index}")
        parts.append(str(item))
    return hashlib.md5(("".join(parts) + SIGN_SALT).encode("utf-8")).hexdigest()


def _extract_png_width(png_bytes: bytes) -> int:
    """从 PNG IHDR 中读取图像宽度。"""

    if png_bytes[:8] != b"\x89PNG\r\n\x1a\n":
        raise ProtocolError("滑块图不是有效的 PNG 数据")
    return struct.unpack(">I", png_bytes[16:20])[0]


def _match_slider(target_bytes: bytes, background_bytes: bytes) -> list[int]:
    """Canny 边缘检测 + 模板匹配定位滑块缺口。"""

    target = cv2.imdecode(np.frombuffer(target_bytes, np.uint8), cv2.IMREAD_ANYCOLOR)
    background = cv2.imdecode(np.frombuffer(background_bytes, np.uint8), cv2.IMREAD_ANYCOLOR)
    if target is None or background is None:
        raise ProtocolError("滑块图或背景图解码失败")
    background = cv2.cvtColor(cv2.Canny(background, 100, 200), cv2.COLOR_GRAY2RGB)
    target = cv2.cvtColor(cv2.Canny(target, 100, 200), cv2.COLOR_GRAY2RGB)
    result = cv2.matchTemplate(background, target, cv2.TM_CCOEFF_NORMED)
    _, _, _, max_loc = cv2.minMaxLoc(result)
    width = target.shape[1]
    return [int(max_loc[0]), int(max_loc[0] + width)]


def _solve_block_puzzle(jigsaw_base64: str, original_base64: str) -> str:
    """计算滑块需要移动的距离，返回 ``{"x": ..., "y": 5}`` JSON 字符串。"""

    target_bytes = base64.b64decode(jigsaw_base64)
    background_bytes = base64.b64decode(original_base64)
    start_x, end_x = _match_slider(target_bytes, background_bytes)
    slider_width = _extract_png_width(target_bytes)
    target_center_x = (start_x + end_x) / 2
    distance = target_center_x - slider_width / 2
    distance = round(distance + random.uniform(-0.1, 0.1), 1)
    return json.dumps({"x": distance, "y": 5}, separators=(",", ":"))


def _merge_user(primary: User, fallback: User) -> User:
    values = {
        item.name: getattr(primary, item.name) or getattr(fallback, item.name)
        for item in fields(User)
    }
    return User(**values)


def _redact_text(value: Any, *, limit: int = 180) -> str:
    text = str(value or "").replace("\r", " ").replace("\n", " ")
    pattern = (
        r"(?i)(password|passwd|pwd|token|authorization|cookie|"
        r"sign|secretkey|phone|captcha)\s*[:=]\s*[^\s,<&]+"
    )
    text = re.sub(pattern, lambda m: m.group(1) + "=<redacted>", text)
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
            raise NetworkError(
                f"接口返回 HTTP {response.status_code}：{method.upper()} {url}"
            )
        return response

    @staticmethod
    def parse_response(response: requests.Response, *, expected_json: bool) -> Any:
        text = response.text
        if not text:
            return {}
        try:
            return response.json()
        except (ValueError, json.JSONDecodeError):
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
    """滑块验证码识别与 ``session/user/v6/login`` 登录编排。"""

    def __init__(self, http: HttpClient) -> None:
        self.http = http

    def _post_json(
        self,
        path: str,
        payload: Mapping[str, Any],
        *,
        headers: Mapping[str, str] | None = None,
    ) -> dict[str, Any]:
        full_headers = dict(DEFAULT_HEADERS)
        if headers:
            full_headers.update(headers)
        response = self.http.request(
            "POST",
            BASE_URL + path,
            json=dict(payload),
            headers=full_headers,
        )
        parsed = self.http.parse_response(response, expected_json=True)
        if not isinstance(parsed, Mapping):
            raise ProtocolError(f"{path} 响应不是 JSON 对象")
        return dict(parsed)

    def solve_block_puzzle(self, max_attempts: int = 5) -> str:
        
        last_error: str = ""
        for attempt in range(max_attempts):
            try:
                client_uid = str(uuid.uuid4()).replace("-", "")
                captcha_info = self._post_json(
                    CAPTCHA_GET_PATH,
                    {
                        "clientUid": client_uid,
                        "captchaType": "blockPuzzle",
                    },
                )
                data = captcha_info.get("data") or {}
                secret_key = str(data.get("secretKey") or "")
                token = str(data.get("token") or "")
                jigsaw = str(data.get("jigsawImageBase64") or "")
                original = str(data.get("originalImageBase64") or "")
                if not secret_key or not token or not jigsaw or not original:
                    raise CaptchaError("验证码响应缺少必要字段")
                slider_data = _solve_block_puzzle(jigsaw, original)
                check_result = self._post_json(
                    CAPTCHA_CHECK_PATH,
                    {
                        "pointJson": aes_encrypt(
                            slider_data,
                            key=secret_key,
                            out_format="b64",
                        ),
                        "token": token,
                        "captchaType": "blockPuzzle",
                    },
                )
                if str(check_result.get("code")) == str(CODE_CAPTCHA_RETRY):
                    last_error = "滑块位置校验未通过，重试中"
                    time.sleep(random.uniform(1, 3))
                    continue
                captcha_payload = f"{token}---{slider_data}"
                return aes_encrypt(captcha_payload, key=secret_key, out_format="b64")
            except GongxueyunLoginError as exc:
                last_error = _redact_text(exc)
                time.sleep(random.uniform(1, 3))
        raise CaptchaError(f"滑块验证码识别失败：{last_error or '未知原因'}")

    def login(self, phone: str, password: str) -> LoginResult:
        """执行一次完整的账号密码登录。"""

        captcha = self.solve_block_puzzle()
        payload = {
            "phone": aes_encrypt(phone),
            "password": aes_encrypt(password),
            "captcha": captcha,
            "loginType": "android",
            "uuid": str(uuid.uuid4()).replace("-", ""),
            "device": DEVICE_NAME,
            "version": APP_VERSION,
            "t": aes_encrypt(str(int(time.time() * 1000))),
        }
        response = self._post_json(LOGIN_PATH, payload)
        if not _business_success(response):
            raise AuthenticationError(_business_message(response) or "登录失败")
        encrypted_data = str(response.get("data") or "").strip()
        if not encrypted_data:
            raise AuthenticationError("登录响应缺少 data 字段")
        try:
            user_payload = json.loads(aes_decrypt(encrypted_data))
        except (ValueError, UnicodeDecodeError) as exc:
            raise ProtocolError("登录响应 data 解密失败") from exc
        if not isinstance(user_payload, Mapping):
            raise ProtocolError("登录响应 data 不是 JSON 对象")
        user = User.from_mapping(user_payload)
        metadata = {
            str(key): value
            for key, value in response.items()
            if key not in {"data"}
        }
        metadata["raw_user"] = dict(user_payload)
        state = SessionState(
            user=user,
            token=user.token,
            expired_time=user.expired_time,
            metadata=metadata,
        )
        if not state.authenticated:
            raise AuthenticationError("登录结果缺少有效 token 或 userId")
        return LoginResult("user_v6_login", state)


class ProfileService:
    """读取当前账号实习计划，失败时明确回退到登录响应。"""

    def __init__(self, http: HttpClient) -> None:
        self.http = http

    def get_plan(self, state: SessionState) -> ProfileResult:
        sign_data = [state.user.user_id, state.user.role_key]
        headers = state.auth_headers()
        headers["sign"] = create_sign(*sign_data)
        payload = {
            "pageSize": 999999,
            "t": aes_encrypt(str(int(time.time() * 1000))),
        }
        try:
            response = self.http.request(
                "POST",
                BASE_URL + PLAN_PATH,
                json=payload,
                headers=headers,
            )
            parsed = self.http.parse_response(response, expected_json=True)
            if not _business_success(parsed):
                raise ProtocolError(_business_message(parsed) or "获取实习计划失败")
            rows = parsed.get("data") if isinstance(parsed, Mapping) else None
            plan_info: dict[str, Any] = {}
            if isinstance(rows, list) and rows:
                first_row = rows[0]
                if isinstance(first_row, Mapping):
                    plan_info = dict(first_row)
            profile = _merge_profile_from_plan(state.user, plan_info)
            return ProfileResult(profile, plan_info, PLAN_PATH)
        except GongxueyunLoginError as exc:
            return ProfileResult(
                state.user,
                {},
                "login_response",
                f"实习计划读取失败，已使用登录响应中的资料：{_redact_text(exc)}",
            )


def _merge_profile_from_plan(user: User, plan_info: Mapping[str, Any]) -> User:
    """将实习计划中的派生字段合并到 User 上（不覆盖已有值）。"""

    derived = User.from_mapping(plan_info)
    values = {
        item.name: getattr(user, item.name) or getattr(derived, item.name)
        for item in fields(User)
    }
    return User(**values)
# ----------------------------- 展示层 -------------------------------------

_PRACTICE_STATE_LABELS: Mapping[str, str] = {
    "1": "未开始",
    "2": "待审核",
    "3": "进行中",
    "4": "已结束",
    "5": "已中止",
}


def _format_expired_time(value: str) -> str:
   
    text = str(value or "").strip()
    if not text:
        return "(未知)"
    try:
        ms = int(text)
    except ValueError:
        return text
    if ms < 10_000_000_000:
        ms *= 1000
    return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(ms / 1000))


def _mask_token(token: str) -> str:
    
    text = str(token or "").strip()
    if len(text) <= 24:
        return text or "(空)"
    return f"{text[:16]}...{text[-4:]}"


def _display_width(text: str) -> int:
    """估算字符串在等宽终端的视觉宽度：CJK 字符算 2，其余算 1。"""

    width = 0
    for char in text:
        code = ord(char)
        if (
            0x1100 <= code <= 0x115F                      # Hangul Jamo
            or 0x2E80 <= code <= 0xA4CF                   # CJK Radicals / 彝文
            or 0xAC00 <= code <= 0xD7A3                   # Hangul Syllables
            or 0xF900 <= code <= 0xFAFF                   # CJK 兼容表意
            or 0xFE30 <= code <= 0xFE4F                   # CJK 兼容形式
            or 0xFF00 <= code <= 0xFF60                   # 全角 ASCII
            or 0xFFE0 <= code <= 0xFFE6                   # 全角符号
            or 0x1F300 <= code <= 0x1FAFF                 # Emoji / 符号补充
            or 0x20000 <= code <= 0x3FFFD                 # CJK 扩展 B-F
        ):
            width += 2
        else:
            width += 1
    return width


def _pad_label(label: str, width: int) -> str:
    """按视觉宽度右填充空格，使后续值列在等宽终端对齐。"""

    pad = width - _display_width(label)
    return label + (" " * pad if pad > 0 else "")


def _kv(label: str, value: Any, *, width: int = 10) -> str:
    
    text = str(value).strip() if value not in (None, "") else ""
    display = text if text else "(未提供)"
    return f"│ {_pad_label(label, width)}  {display}"


def _format_report_progress(plan_paper: Mapping[str, Any] | None) -> str:
    
    if not isinstance(plan_paper, Mapping) or not plan_paper:
        return "│ (无报告配置数据)"
    parts: list[str] = []
    spec = (
        ("日报", "paperReportCount", "dayPaperNum", "dayPaper"),
        ("周报", "weekReportCount", "maxWeekNum", "weekPaper"),
        ("月报", "monthReportCount", "monthPaperNum", "monthPaper"),
        ("总结", "summaryReportCount", "summaryPaperNum", "summaryPaper"),
    )
    for label, count_key, limit_key, enabled_key in spec:
        enabled = str(plan_paper.get(enabled_key)).lower() not in {"false", "0", "none", ""}
        if not enabled:
            continue
        count = plan_paper.get(count_key)
        limit = plan_paper.get(limit_key)
        parts.append(f"{label} {count}/{limit}")
    return "│ " + "   ".join(parts) if parts else "│ (无报告数据)"


def _format_session_summary(login: LoginResult, profile: ProfileResult) -> str:

    user = profile.profile
    plan = profile.plan_info or {}
    lines: list[str] = []
    width = 76

    lines.append("┌─ 登录成功 " + "─" * (width - 7))
    lines.append(_kv("登录链路", login.method))
    lines.append(_kv("资料来源", profile.source))
    if profile.warning:
        lines.append(_kv("警告", profile.warning))

    lines.append("├─ 账号信息 " + "─" * (width - 7))
    lines.append(_kv("用户ID", user.user_id))
    lines.append(_kv("手机号", user.phone))
    identity = f"{user.user_type or '-'}/{user.role_key or '-'}"
    lines.append(_kv("身份", identity))
    name_display = user.name or user.username
    lines.append(_kv("姓名/昵称", name_display))
    if user.class_name:
        lines.append(_kv("班级", user.class_name))
    if user.college:
        lines.append(_kv("院系", user.college))
    if user.major:
        lines.append(_kv("专业", user.major))
    if user.student_number:
        lines.append(_kv("学号", user.student_number))
    lines.append(_kv("Token", _mask_token(user.token)))
    lines.append(_kv("过期时间", _format_expired_time(user.expired_time)))

    if plan:
        lines.append("├─ 实习计划 " + "─" * (width - 7))
        lines.append(_kv("计划名称", plan.get("planName")))
        lines.append(_kv("学期", plan.get("semester")))
        start = str(plan.get("startTime") or "")[:10]
        end = str(plan.get("endTime") or "")[:10]
        if start and end:
            lines.append(_kv("起止时间", f"{start} ~ {end}"))
        state_raw = str(plan.get("practiceState") or "")
        state_label = _PRACTICE_STATE_LABELS.get(state_raw, "")
        state_display = f"{state_label or '未知'}" + (
            f" (practiceState={state_raw})" if state_raw else ""
        )
        lines.append(_kv("实习状态", state_display))
        lines.append(_kv("指导老师", plan.get("createName")))
        lines.append(_kv("计划ID", plan.get("planId")))
        lines.append("├─ 报告进度 " + "─" * (width - 7))
        lines.append(_format_report_progress(plan.get("planPaper")))

    lines.append("└" + "─" * (width + 2))
    return "\n".join(lines)


class GongxueyunLoginClient:
        
    def __init__(self, session: requests.Session | None = None) -> None:
        self.http = HttpClient(session)
        self.auth = AuthService(self.http)
        self.profile = ProfileService(self.http)

    def login_and_get_profile(
        self,
        phone: str,
        password: str,
    ) -> tuple[LoginResult, ProfileResult]:
        login = self.auth.login(phone, password)
        return login, self.profile.get_plan(login.state)

    def close(self) -> None:
        self.http.close()

    def __enter__(self) -> GongxueyunLoginClient:
        return self

    def __exit__(self, exc_type, exc, traceback) -> None:
        self.close()


class InteractiveLoginApp:
    """命令行交互入口。"""

    def run(self) -> None:
        print("工学云一键登录")
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
            except GongxueyunLoginError as exc:
                print(f"操作失败：{exc}")
            except Exception as exc:
                print(f"操作失败：{type(exc).__name__}：{exc}")

    @staticmethod
    def _login_flow() -> None:
        phone = input("手机号：").strip()
        if not phone:
            print("手机号不能为空。")
            return
        password = getpass("密码：")
        if not password:
            print("密码不能为空。")
            return
        print("正在登录并读取账号资料...")
        with GongxueyunLoginClient() as client:
            login, profile = client.login_and_get_profile(phone, password)
        print()
        print(_format_session_summary(login, profile))


def main() -> int:
    InteractiveLoginApp().run()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
