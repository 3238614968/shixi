"""今日校园登录。

本文件只保留以下链路：

1. 学校租户列表和学校入口自动发现；
2. 学校统一认证账号密码登录；
3. 原生短信验证码登录；
4. 登录后读取当前账号资料；
5. 以交互式菜单运行，不保存账号、密码、验证码和 Cookie。

运行时只需要安装 requests 和 pycryptodome。
本脚本不提供验证码识别、验证码绕过或风控规避功能；若服务端要求图形验证码或滑块验证，脚本会停止当前登录流程。

更新内容：
1. 2024-06-30：修复账号密码登录逻辑。
2. 2026-07-20：删除验证码识别逻辑，保留账号密码登录和原生短信登录。
3. 2026-07-20：修复删除 OCR 后遗留的方法调用和启动依赖错误。

@author: xiaohai
@date: 2026-07-20
@license: MIT
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import secrets
import tempfile
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from html.parser import HTMLParser
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import parse_qs, urlencode, urljoin, urlparse


SCRIPT_DIR = Path(__file__).resolve().parent
RUNTIME_DIR = SCRIPT_DIR / "runtime"
TEMP_DIR = RUNTIME_DIR / "temp"
CACHE_DIR = RUNTIME_DIR / "cache"
for directory in (TEMP_DIR, CACHE_DIR):
    directory.mkdir(parents=True, exist_ok=True)
for environment_key in ("TEMP", "TMP", "TMPDIR"):
    os.environ[environment_key] = str(TEMP_DIR)
os.environ["XDG_CACHE_HOME"] = str(CACHE_DIR)
tempfile.tempdir = str(TEMP_DIR)

import requests
from Crypto.Cipher import AES, DES, PKCS1_v1_5
from Crypto.PublicKey import RSA
from Crypto.Util.Padding import pad, unpad
from requests.adapters import HTTPAdapter
from urllib3 import disable_warnings
from urllib3.exceptions import InsecureRequestWarning
from urllib3.util.retry import Retry


# ---------------------------------------------------------------------------
# 基础异常
# ---------------------------------------------------------------------------


class CampusError(Exception):
    """脚本基础异常。"""


class NetworkError(CampusError):
    """网络请求异常。"""


class ProtocolError(CampusError):
    """服务端协议结构异常。"""


class LoginError(CampusError):
    """登录流程异常。"""


# ---------------------------------------------------------------------------
# 数据模型
# ---------------------------------------------------------------------------


@dataclass
class Tenant:
    """学校租户信息。"""

    tenant_id: str
    name: str
    join_type: str = ""
    ids_url: str = ""
    amp_url: str = ""
    amp_url2: str = ""
    host: str = ""
    login_url: str = ""
    raw: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        """把租户对象转换为普通字典。"""
        return {
            "tenant_id": self.tenant_id,
            "name": self.name,
            "join_type": self.join_type,
            "ids_url": self.ids_url,
            "amp_url": self.amp_url,
            "amp_url2": self.amp_url2,
            "host": self.host,
            "login_url": self.login_url,
        }


@dataclass(frozen=True)
class AccountIdentity:
    """从账号输入中拆出的真实账号和学校线索。"""

    login_name: str
    hints: tuple[str, ...]


@dataclass(frozen=True)
class NativeServiceSecret:
    """原生短信链路返回的动态服务密钥。"""

    random_string: str
    cpdaily_secret: str
    cat_secret: str


@dataclass
class NativeLoginResult:
    """原生短信登录结果。"""

    tenant_id: str
    tenant_name: str
    mobile: str
    device_status: str
    session_token: str
    tgc: str
    profile: dict[str, Any]


# ---------------------------------------------------------------------------
# 原生登录内置密钥
# ---------------------------------------------------------------------------

NATIVE_PUBLIC_KEY_PEM = """-----BEGIN PUBLIC KEY-----
MIGfMA0GCSqGSIb3DQEBAQUAA4GNADCBiQKBgQCpwqE77zx+WexQWf1qDzb8EGey
et7VO78JiCDrZLcesaGjN5B8s66bMCfcn9R3GN25/EA3lFPI86hgluMPT6X1rneW
QRdKMaFWtxZLc+0Gdkf8zvdPf3rcYt6VjPnq3Hu1iSdytD8SIuTcSGFoPctId7jZ
zEjMjj74mnu3WtihZQIDAQAB
-----END PUBLIC KEY-----"""

NATIVE_PRIVATE_KEY_PEM = """-----BEGIN PRIVATE KEY-----
MIICdQIBADANBgkqhkiG9w0BAQEFAASCAl8wggJbAgEAAoGBAKcyZ9yEReNLggED
LYqJVXKF4ZNDp/9sET7D3Dt7VZJKH8iK+KqjozEvT16E1RYpfjTmzXcGIbicVH6k
Htzy14+kzh8v28fY/a8Vd9Ot9v+eT6Jlze3uw2HsyFbad9Pl8x8d5rjMp8xHHXU+
qLvKiEzOmTvB+MDTyAnhPc42Q85HAgMBAAECgYAdny2NgRXMtkT7HvADml88IgIc
ECGEfEX148dx9mDrwRwucIir2r//58zdBxWljoZgov+F9d0lkvTZVwRsys1rySqp
BpDUB+WIQuYMHGqrf4ByZ+136TsSyXuKQ7PzOJ22HXnjth8QANS2ulFY9nE+ZpB8
9vEBoatDkJ9dx2TZ6QJBANvNYkchnkqAjXxYD5A///gQ1LZ2JLY4HB7WzIFRQNft
IXUmfyEWPYSpTdIroWoNInejJNZJStAFT2Bfq/IaN70CQQDCuzz7NOmq2iuqI20E
GY4qDMGjcJJT7ZWmeGRVADwKaLS4VrifZy201ZJxwaqTaFb9wd45whncaDz22S+t
QGxTAkBeqoyDWkVUjR1iyoKZfBcAfi8/Do8tM+lYluapY5dr6COa0yO52lxQgKKV
vFje1h1cLZW1/QcNpNvVBB+IPCZ5AkA/UyRBjLNwHAKXEW4iJy1T/1H5FGKBaIGB
4SS/f5QGzoX2bD0dmTAD3nABDjmqNgQUATeDENvYEQ3COF6IuKqBAkAxefuDjLbT
wtVE14AhMxnNt58HlOeNLUICipkq/cZBgkseHCurPEiXXVDARIA4nj82YTqKjXrp
mI/+1VLKBQ9Z
-----END PRIVATE KEY-----"""


# ---------------------------------------------------------------------------
# 通用 HTTP 客户端
# ---------------------------------------------------------------------------


disable_warnings(InsecureRequestWarning)


class HttpClient:
    """当前运行实例使用的短生命周期 HTTP 会话。"""

    def __init__(self) -> None:
        """创建不会读取或写入本地 Cookie 文件的会话。"""
        self.session = requests.Session()
        self.host = ""
        self.last_response: requests.Response | None = None
        self.server_time_offset = 0.0
        self.device_id = str(uuid.uuid4()).upper()
        self.system_version = "13"
        self.model = "CPDAILY-PYTHON"
        self.app_version = "9.9.20"
        self.build_id = "TKQ1.221114.001"
        self.webview_version = "108.0.5359.128"
        self.timeout = (10.0, 30.0)
        self.verify_tls = True
        self.session.headers.update(
            {
                "User-Agent": (
                    f"Mozilla/5.0 (Linux; Android {self.system_version}; "
                    f"{self.model} Build/{self.build_id}; wv) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 "
                    f"Chrome/{self.webview_version} Mobile Safari/537.36 "
                    f"cpdaily/{self.app_version} wisedu/{self.app_version}"
                ),
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
        adapter = HTTPAdapter(
            max_retries=retry,
            pool_connections=10,
            pool_maxsize=10,
        )
        self.session.mount("http://", adapter)
        self.session.mount("https://", adapter)

    def set_host(self, host: str) -> None:
        """设置学校业务接口根地址。"""
        self.host = host.rstrip("/") + "/"

    def activate_portal_session(self) -> dict[str, Any]:
        
        summary: dict[str, Any] = {"attempted": False}
        if not self.host:
            return summary
        candidates = (
            urljoin(self.host, "portal/login"),
            urljoin(self.host, "portal/"),
            self.host,
        )
        errors: list[dict[str, Any]] = []
        for url in candidates:
            try:
                response = self.get(url, allow_redirects=True)
            except CampusError as exc:
                errors.append({"url": url, "error": str(exc)})
                continue
            summary["attempted"] = True
            summary["final_url"] = response.url
            summary["status"] = response.status_code
            if errors:
                summary["prior_errors"] = errors
            return summary
        summary["errors"] = errors
        return summary

    def make_url(self, path_or_url: str) -> str:
        """把相对地址拼接成完整地址。"""
        if path_or_url.startswith(("http://", "https://")):
            return path_or_url
        if not self.host:
            raise NetworkError("尚未设置业务接口根地址")
        return urljoin(self.host, path_or_url.lstrip("/"))

    def request(
        self,
        method: str,
        path_or_url: str,
        **kwargs: Any,
    ) -> requests.Response:
        """发送请求，并记录最近一次响应。"""
        url = self.make_url(path_or_url)
        kwargs.setdefault("timeout", self.timeout)
        kwargs.setdefault("verify", self.verify_tls)
        try:
            response = self.session.request(method, url, **kwargs)
        except requests.RequestException as exc:
            raise NetworkError(f"请求失败：{method.upper()} {url}：{exc}") from exc
        self.last_response = response
        self._update_server_time(response)
        if response.status_code == 418:
            raise NetworkError("服务端返回 HTTP 418，请稍后重试")
        return response

    def get(self, path_or_url: str, **kwargs: Any) -> requests.Response:
        """发送 GET 请求。"""
        return self.request("GET", path_or_url, **kwargs)

    def post(self, path_or_url: str, **kwargs: Any) -> requests.Response:
        """发送 POST 请求。"""
        return self.request("POST", path_or_url, **kwargs)

    def post_json(
        self,
        path_or_url: str,
        payload: dict[str, Any] | list[Any] | None = None,
        *,
        headers: dict[str, str] | None = None,
        check_http: bool = True,
    ) -> dict[str, Any]:
        """发送 JSON 请求并返回对象。"""
        merged_headers = {"Content-Type": "application/json; charset=utf-8"}
        if headers:
            merged_headers.update(headers)
        response = self.post(
            path_or_url,
            data=json.dumps(
                payload if payload is not None else {},
                ensure_ascii=False,
            ),
            headers=merged_headers,
        )
        if check_http and response.status_code >= 400:
            raise NetworkError(
                f"接口返回 HTTP {response.status_code}："
                f"{response.text[:300]}"
            )
        try:
            body = response.json()
        except ValueError as exc:
            raise ProtocolError(
                f"接口未返回 JSON：{response.text[:300]}"
            ) from exc
        if not isinstance(body, dict):
            raise ProtocolError("接口 JSON 根节点不是对象")
        return body

    @staticmethod
    def data_of(body: dict[str, Any]) -> Any:
        """提取常见的业务数据字段。"""
        for key in ("datas", "data", "result"):
            if key in body:
                return body[key]
        return body

    @staticmethod
    def is_success(body: dict[str, Any]) -> bool:
        """识别常见的成功响应。"""
        code = body.get("code", body.get("resultCode"))
        message = str(body.get("message", body.get("msg", ""))).upper()
        if code in (0, 200, "0", "200", "SUCCESS"):
            return True
        if code in (
            -1,
            400,
            401,
            403,
            404,
            500,
            "-1",
            "400",
            "401",
            "403",
            "404",
            "500",
        ):
            return False
        if any(word in message for word in ("失败", "错误", "ERROR", "FAIL")):
            return False
        if message in ("SUCCESS", "OK", "操作成功", "提交成功"):
            return True
        for key in ("datas", "data", "result"):
            if code is None and body.get(key) not in (None, False, ""):
                return True
        return False

    def _update_server_time(self, response: requests.Response) -> None:
        """根据 Date 响应头估算时间差。"""
        raw = response.headers.get("Date")
        if not raw:
            return
        try:
            server_dt = parsedate_to_datetime(raw)
            if server_dt.tzinfo is None:
                server_dt = server_dt.replace(tzinfo=timezone.utc)
            self.server_time_offset = (
                server_dt - datetime.now(timezone.utc)
            ).total_seconds()
        except (TypeError, ValueError, OverflowError):
            return


# ---------------------------------------------------------------------------
# 学校自动发现
# ---------------------------------------------------------------------------


TENANT_LIST_URL = "https://mobile.campushoy.com/v6/config/guest/tenant/list"
TENANT_INFO_URL = "https://mobile.campushoy.com/v6/config/guest/tenant/info"
CAMPUS_CAS_SERVICE_URL = "https://mobile.campushoy.com/v6/auth/campus/cas/login"

GENERIC_DOMAIN_LABELS = {
    "www",
    "mail",
    "student",
    "stu",
    "sso",
    "auth",
    "authserver",
    "cas",
    "iap",
    "campusphere",
    "campushoy",
    "edu",
    "com",
    "net",
    "org",
    "cn",
}


def parse_account_identity(value: str) -> AccountIdentity:
    
    account = value.strip()
    hints: list[str] = []
    for separator in ("::", "|", "\\"):
        if separator not in account:
            continue
        hint, login_name = account.split(separator, 1)
        if hint.strip() and login_name.strip():
            hints.append(hint.strip())
            account = login_name.strip()
            break
    if "@" in account:
        _, domain = account.rsplit("@", 1)
        if domain.strip():
            hints.append(domain.strip())
    return AccountIdentity(account, tuple(dict.fromkeys(hints)))


def _compact(value: str) -> str:
    """保留中英文和数字，用于学校名称比较。"""
    return "".join(re.findall(r"[\w\u4e00-\u9fff]+", value.lower()))


def _hostname(value: str) -> str:
    """提取 URL 或域名中的主机名。"""
    raw = value.strip().lower().lstrip(".")
    if not raw:
        return ""
    parsed = urlparse(raw if "://" in raw else f"//{raw}")
    return (parsed.hostname or "").lower().lstrip(".")


def _domain_labels(value: str) -> set[str]:
    """提取学校域名的有效标签。"""
    host = _hostname(value)
    return {
        label
        for label in host.split(".")
        if len(label) >= 3 and label not in GENERIC_DOMAIN_LABELS
    }


class TenantService:
    """负责学校租户列表、学校详情和认证入口解析。"""

    def __init__(self, http: HttpClient) -> None:
        self.http = http
        self._cache: list[dict[str, Any]] | None = None

    def list_tenants(self, refresh: bool = False) -> list[dict[str, Any]]:
        """读取官方学校租户列表。"""
        if self._cache is not None and not refresh:
            return self._cache
        response = self.http.get(TENANT_LIST_URL)
        if response.status_code >= 400:
            raise NetworkError(f"学校列表返回 HTTP {response.status_code}")
        try:
            body = response.json()
        except ValueError as exc:
            raise ProtocolError("学校列表不是 JSON") from exc
        data = body.get("data", body.get("datas", []))
        if not isinstance(data, list):
            raise ProtocolError("学校列表结构异常")
        self._cache = data
        return data

    def search(self, keyword: str) -> list[Tenant]:
        """按学校名称、租户代码或域名搜索学校。"""
        key = keyword.strip()
        result: list[tuple[int, Tenant]] = []
        for item in self.list_tenants():
            tenant = self._to_tenant(item)
            if not tenant.name and not tenant.tenant_id:
                continue
            score = self._score_tenant(tenant, (key,))
            if score:
                result.append((score, tenant))
        result.sort(key=lambda row: (-row[0], row[1].name))
        return [tenant for _, tenant in result]

    def detect_from_account(
        self,
        account: str,
    ) -> tuple[Tenant, AccountIdentity]:
        """根据账号中的学校线索自动识别唯一学校。"""
        identity = parse_account_identity(account)
        if not identity.hints:
            raise ProtocolError(
                "账号中没有学校线索，请输入“学校名称::账号”或校园邮箱"
            )
        scored: list[tuple[int, Tenant]] = []
        for item in self.list_tenants():
            tenant = self._to_tenant(item)
            if tenant.join_type == "NONE":
                continue
            score = self._score_tenant(tenant, identity.hints)
            if score:
                scored.append((score, tenant))
        if not scored:
            raise ProtocolError("没有根据账号线索匹配到学校")
        scored.sort(key=lambda row: (-row[0], row[1].name))
        best_score, best = scored[0]
        tied = [tenant for score, tenant in scored if score == best_score]
        if best_score < 120 or len(tied) != 1:
            names = "、".join(tenant.name for tenant in tied[:6])
            raise ProtocolError(f"学校匹配不唯一：{names}")
        return best, identity

    @staticmethod
    def _to_tenant(item: dict[str, Any]) -> Tenant:
        """把列表项转换为租户对象。"""
        return Tenant(
            tenant_id=str(item.get("id", item.get("tenantId", ""))),
            name=str(item.get("name", "")),
            join_type=str(item.get("joinType", "")),
            ids_url=str(item.get("idsUrl", "") or ""),
            amp_url=str(item.get("ampUrl", "") or ""),
            amp_url2=str(item.get("ampUrl2", "") or ""),
            raw=item,
        )

    @staticmethod
    def _score_tenant(tenant: Tenant, hints: Iterable[str]) -> int:
        """计算学校与账号线索的匹配分。"""
        item = tenant.raw
        name_key = _compact(tenant.name)
        code_key = _compact(str(item.get("tenantCode", "")))
        urls = (
            tenant.ids_url,
            str(item.get("casLoginUrl", "") or ""),
            tenant.amp_url,
            tenant.amp_url2,
        )
        hosts = {_hostname(value) for value in urls if _hostname(value)}
        labels: set[str] = set()
        for host in hosts:
            labels.update(_domain_labels(host))
        best = 0
        for hint in hints:
            hint_key = _compact(hint)
            hint_host = _hostname(hint)
            hint_labels = _domain_labels(hint)
            if code_key and hint_key == code_key:
                best = max(best, 260)
            if name_key and hint_key == name_key:
                best = max(best, 250)
            elif (
                name_key
                and len(hint_key) >= 4
                and (hint_key in name_key or name_key in hint_key)
            ):
                best = max(best, 190)
            for host in hosts:
                if hint_host and (
                    hint_host == host
                    or hint_host.endswith(f".{host}")
                    or host.endswith(f".{hint_host}")
                ):
                    best = max(best, 240)
            shared = hint_labels & labels
            if shared:
                best = max(best, 150 + min(60, 20 * (len(shared) - 1)))
            if hint_key and hint_key in labels:
                best = max(best, 180)
        return best

    def load_info(self, tenant: Tenant) -> Tenant:
        """补全学校认证地址和业务接口地址。"""
        response = self.http.get(
            TENANT_INFO_URL,
            params={"ids": tenant.tenant_id},
        )
        if response.status_code >= 400:
            raise NetworkError(f"学校详情返回 HTTP {response.status_code}")
        body = response.json()
        rows = body.get("data", body.get("datas", []))
        if not isinstance(rows, list) or not rows:
            raise ProtocolError("学校详情为空")
        item = rows[0]
        tenant.join_type = str(item.get("joinType", tenant.join_type))
        tenant.ids_url = str(item.get("idsUrl", "") or "")
        tenant.amp_url = str(item.get("ampUrl", "") or "")
        tenant.amp_url2 = str(item.get("ampUrl2", "") or "")
        tenant.raw = item
        tenant.host, tenant.login_url = self._resolve_entry(tenant)
        return tenant

    def _resolve_entry(self, tenant: Tenant) -> tuple[str, str]:
        """解析业务域名，并跟随认证入口重定向。"""
        fallback_host = ""
        wecloud_url = str(tenant.raw.get("wecloudUrl", "") or "")
        wecloud_parsed = urlparse(wecloud_url)
        if wecloud_parsed.scheme and wecloud_parsed.netloc:
            fallback_host = (
                f"{wecloud_parsed.scheme}://{wecloud_parsed.netloc}/"
            )

        ids_parsed = urlparse(tenant.ids_url)
        if (
            tenant.join_type.upper() == "CLOUD"
            and ids_parsed.scheme
            and ids_parsed.netloc
            and "/iap" in ids_parsed.path.lower()
        ):
            if not fallback_host:
                for entry in (tenant.amp_url, tenant.amp_url2):
                    parsed_entry = urlparse(entry)
                    if parsed_entry.scheme and parsed_entry.netloc:
                        fallback_host = (
                            f"{parsed_entry.scheme}://{parsed_entry.netloc}/"
                        )
                        break
            if not fallback_host:
                fallback_host = f"{ids_parsed.scheme}://{ids_parsed.netloc}/"
            return fallback_host, self._build_iap_login_url(tenant.ids_url)

        for entry in (tenant.amp_url, tenant.amp_url2):
            if not entry:
                continue
            parsed = urlparse(entry)
            if not parsed.scheme or not parsed.netloc:
                continue
            host = f"{parsed.scheme}://{parsed.netloc}/"
            fallback_host = fallback_host or host
            current = entry
            try:
                for _ in range(12):
                    response = self.http.get(current, allow_redirects=False)
                    location = response.headers.get("Location")
                    if response.is_redirect and location:
                        current = urljoin(current, location)
                        continue
                    current = response.url or current
                    break
                return host, current
            except Exception:
                continue
        if fallback_host and tenant.ids_url:
            return fallback_host, tenant.ids_url
        if tenant.ids_url:
            parsed = urlparse(tenant.ids_url)
            if parsed.scheme and parsed.netloc:
                return f"{parsed.scheme}://{parsed.netloc}/", tenant.ids_url
        raise ProtocolError("学校详情没有可用的认证入口")

    @staticmethod
    def _build_iap_login_url(ids_url: str) -> str:
        """把学校 idsUrl 转换为今日校园移动端 CAS 登录入口。"""
        base = ids_url.rstrip("/")
        if not base.lower().endswith("/login"):
            base += "/login"
        return f"{base}?{urlencode({'service': CAMPUS_CAS_SERVICE_URL})}"


# ---------------------------------------------------------------------------
# 统一认证账号密码登录
# ---------------------------------------------------------------------------


@dataclass
class ParsedForm:
    """HTML 登录表单。"""

    form_id: str = ""
    action: str = ""
    method: str = "post"
    inputs: list[dict[str, str]] = field(default_factory=list)


@dataclass(frozen=True)
class IapLoginContext:
    """一次 IAP 登录页面协商得到的动态字段。"""

    auth_host: str
    page_url: str
    lt_hint: str
    dllt: str
    public_key_der_b64: str


class FormParser(HTMLParser):
    """只解析登录所需的 form 和 input。"""

    def __init__(self) -> None:
        super().__init__()
        self.forms: list[ParsedForm] = []
        self.current: ParsedForm | None = None

    def handle_starttag(
        self,
        tag: str,
        attrs: list[tuple[str, str | None]],
    ) -> None:
        values = {key.lower(): value or "" for key, value in attrs}
        if tag.lower() == "form":
            self.current = ParsedForm(
                form_id=values.get("id", ""),
                action=values.get("action", ""),
                method=values.get("method", "post").lower(),
            )
            self.forms.append(self.current)
        elif tag.lower() == "input" and self.current is not None:
            self.current.inputs.append(values)

    def handle_endtag(self, tag: str) -> None:
        if tag.lower() == "form":
            self.current = None


def pkcs7_pad(data: bytes, block_size: int) -> bytes:
    """执行 PKCS#7 填充。"""
    count = block_size - len(data) % block_size
    return data + bytes([count]) * count


def encrypt_cas_password(password: str, salt: str) -> str:
    key = salt.encode("utf-8")
    if len(key) not in (16, 24, 32):
        raise ValueError("统一认证 AES 盐值长度异常")
    alphabet = "ABCDEFGHJKMNPQRSTWXYZabcdefhijkmnprstwxyz2345678"
    randomizer = secrets.SystemRandom()
    iv = "".join(randomizer.choice(alphabet) for _ in range(16)).encode()
    prefix = "".join(randomizer.choice(alphabet) for _ in range(64))
    plain = pkcs7_pad((prefix + password).encode("utf-8"), AES.block_size)
    encrypted = AES.new(key, AES.MODE_CBC, iv).encrypt(plain)
    return base64.b64encode(encrypted).decode("ascii")


IAP_RSA_PUBLIC_KEY_DER_B64 = (
    "MIGfMA0GCSqGSIb3DQEBAQUAA4GNADCBiQKBgQDCpbRy8ZoyQvRPpUDIXycglTwV"
    "DcYrLcv7P9HI4E7/TAPZiI3GN0ckTUVVWRvoo/re3uCOOJK+F+Ufh19XiRIdoPYC"
    "ULsSyEjcLLiyAS09mVOzhAQco84E/lM24T7rRTVID7LIgWPewyN8Nd5vzHET4Q3q"
    "TthoL8n82BwC1iXuVQIDAQAB"
)


def encrypt_iap_password(
    password: str,
    public_key_der_b64: str = IAP_RSA_PUBLIC_KEY_DER_B64,
) -> str:
    try:
        public_key = RSA.import_key(
            base64.b64decode(public_key_der_b64, validate=True)
        )
    except (ValueError, TypeError, IndexError) as exc:
        raise ValueError("IAP RSA 公钥格式无效") from exc
    encrypted = PKCS1_v1_5.new(public_key).encrypt(password.encode("utf-8"))
    return "{rsa}" + base64.b64encode(encrypted).decode("ascii")


def generate_legacy_rsa_password(
    password: str,
    modulus_hex: str,
    exponent_hex: str,
) -> str:
    modulus = int(modulus_hex, 16)
    exponent = int(exponent_hex, 16)
    key_size = (modulus.bit_length() + 7) // 8
    message = password.encode("utf-8")[::-1]
    if len(message) > key_size - 3:
        raise ValueError("密码长度超过旧 RSA 页面允许范围")
    padded = (
        b"\x00\x00"
        + b"\x00" * (key_size - len(message) - 3)
        + b"\x00"
        + message
    )
    encrypted = pow(int.from_bytes(padded, "big"), exponent, modulus)
    return encrypted.to_bytes(key_size, "big").hex()


class PasswordAuthService:
    """处理 IAP、CAS 和 authserver 账号密码登录。"""

    def __init__(self, http: HttpClient) -> None:
        self.http = http
        self._iap_public_key_der_b64 = ""
        self._iap_device_id = http.device_id
        self._iap_fingerprint_id = uuid.uuid4().hex

    def login(self, username: str, password: str, login_url: str) -> None:
        """根据登录地址自动选择认证类型。"""
        if "/iap" in login_url.lower():
            self._login_iap(username, password, login_url)
        else:
            self._login_cas(username, password, login_url)

    def _login_iap(
        self,
        username: str,
        password: str,
        login_url: str,
    ) -> None:
        """执行新版 IAP Vue 登录链。

        本项目不处理图形验证码和滑块验证。服务端要求验证码时，
        立即停止当前流程，避免误导使用者认为脚本能够绕过验证。
        """
        context = self._open_iap_context(login_url)
        ajax_headers = self._iap_ajax_headers(context)
        lt_response = self.http.post(
            urljoin(context.auth_host, "iap/security/lt"),
            data={"lt": context.lt_hint},
            headers=ajax_headers,
        )
        if lt_response.status_code >= 400:
            raise LoginError(
                f"IAP 动态票据接口返回 HTTP {lt_response.status_code}"
            )
        try:
            lt_body = lt_response.json()
        except ValueError as exc:
            raise LoginError(
                f"IAP 动态票据接口未返回 JSON：HTTP {lt_response.status_code}"
            ) from exc

        lt = self._find_first(lt_body, {"_lt", "lt", "ltId"})
        if not lt:
            raise LoginError("IAP 未返回登录票据")

        need_value = self._find_first(
            lt_body,
            {"needCaptcha", "isNeed", "validation"},
        )
        if need_value is None:
            need_response = self.http.post(
                urljoin(context.auth_host, "iap/checkNeedCaptcha"),
                data={"username": username, "lt": str(lt)},
                headers=ajax_headers,
            )
            if need_response.status_code < 400:
                try:
                    need_body = need_response.json()
                except ValueError:
                    need_body = {}
                need_value = self._find_first(
                    need_body,
                    {"needCaptcha", "isNeed", "validation"},
                )

        if self._as_bool(need_value):
            raise LoginError(
                "当前统一认证要求图形验证码，本脚本不提供验证码识别或绕过。"
                "请先在学校官方认证页面或官方客户端完成验证后再重试。"
            )

        form = {
            "lt": str(lt),
            "rememberMe": "false",
            "dllt": context.dllt,
            "mobile": "",
            "username": username,
            "password": encrypt_iap_password(
                password,
                context.public_key_der_b64,
            ),
            "captcha": "",
            "deviceId": self._iap_device_id,
            "fingerprintId": self._iap_fingerprint_id,
        }
        response = self.http.post(
            urljoin(context.auth_host, "iap/doLogin"),
            data=form,
            headers=self._iap_ajax_headers(
                context,
                device_id=self._iap_device_id,
                fingerprint_id=self._iap_fingerprint_id,
            ),
            allow_redirects=False,
        )
        location = response.headers.get("Location")
        if response.is_redirect and location:
            self._follow_iap_redirect(
                urljoin(context.auth_host, location)
            )
            return

        try:
            body = response.json()
        except ValueError as exc:
            raise LoginError(
                f"IAP 登录失败：HTTP {response.status_code}"
            ) from exc

        code = str(
            self._find_first(body, {"resultCode", "code", "status"}) or ""
        ).upper()
        message = str(
            self._find_first(
                body,
                {"message", "msg", "resultMessage"},
            )
            or ""
        )
        jump_value = self._find_first(
            body,
            {"url", "redirectUrl", "location"},
        )

        if code == "REDIRECT":
            if not jump_value:
                raise LoginError("IAP 登录成功响应缺少跳转地址")
            self._follow_iap_redirect(
                urljoin(context.auth_host, str(jump_value))
            )
            return
        if code in {"SUCCESS", "OK", "200"}:
            if jump_value:
                self._follow_iap_redirect(
                    urljoin(context.auth_host, str(jump_value))
                )
            return
        if code in {"FAIL_UPNOTMATCH", "UPNOTMATCH"}:
            raise LoginError("用户名或密码不匹配")
        if code in {"CAPTCHA_NOTMATCH", "CAPTCHA_ERROR"} or self._is_captcha_error(
            message
        ):
            raise LoginError(
                "服务端要求或拒绝了图形验证码，本脚本不提供验证码处理。"
                "请在官方认证页面完成验证后再重试。"
            )
        raise LoginError(f"IAP 登录失败：{message or code or '未知错误'}")

    def _open_iap_context(self, login_url: str) -> IapLoginContext:
        """访问 IAP 登录入口并读取动态 LT、来源页和 RSA 公钥。"""
        response = self.http.get(
            login_url,
            allow_redirects=True,
            headers={
                "Accept": (
                    "text/html,application/xhtml+xml,application/xml;q=0.9,"
                    "image/avif,image/webp,image/apng,*/*;q=0.8"
                ),
                "Cache-Control": "no-cache",
                "Pragma": "no-cache",
                "Upgrade-Insecure-Requests": "1",
                "cpdailyauthtype": "Login",
                "X-Requested-With": "com.wisedu.cpdaily",
            },
        )
        page_url = response.url or login_url
        parsed = urlparse(page_url)
        if not parsed.scheme or not parsed.netloc:
            parsed = urlparse(login_url)
            page_url = login_url
        if not parsed.scheme or not parsed.netloc:
            raise LoginError("IAP 登录地址格式无效")
        query = parse_qs(parsed.query)
        if not query:
            query = parse_qs(urlparse(login_url).query)
        lt_hint = str((query.get("_2lBepC") or query.get("lt") or [""])[0])
        dllt = str((query.get("_dllt") or query.get("dllt") or ["cpdaily"])[0])
        return IapLoginContext(
            auth_host=f"{parsed.scheme}://{parsed.netloc}/",
            page_url=page_url,
            lt_hint=lt_hint,
            dllt=dllt or "cpdaily",
            public_key_der_b64=self._discover_iap_public_key(
                page_url,
                response.text,
            ),
        )

    def _discover_iap_public_key(self, page_url: str, html: str) -> str:
        """优先从当前登录前端发现公钥，并保留归档公钥作为兼容值。"""
        if self._iap_public_key_der_b64:
            return self._iap_public_key_der_b64
        key = self._extract_iap_public_key(html)
        if key:
            self._iap_public_key_der_b64 = key
            return key
        script_urls = re.findall(
            r"<script[^>]+src=[\"']([^\"']+)[\"']",
            html,
            re.I,
        )
        script_urls.sort(
            key=lambda value: (
                "chunk-common" not in value.lower(),
                "common" not in value.lower(),
            )
        )
        for script_url in script_urls[:8]:
            try:
                script_response = self.http.get(
                    urljoin(page_url, script_url),
                    headers={"Referer": page_url},
                )
            except Exception:
                continue
            key = self._extract_iap_public_key(script_response.text)
            if key:
                self._iap_public_key_der_b64 = key
                return key
        self._iap_public_key_der_b64 = IAP_RSA_PUBLIC_KEY_DER_B64
        return self._iap_public_key_der_b64

    @staticmethod
    def _extract_iap_public_key(source: str) -> str:
        """从压缩 JavaScript 中筛选可导入的 DER Base64 RSA 公钥。"""
        for candidate in re.findall(
            r"(?<![A-Za-z0-9+/])(MIG[A-Za-z0-9+/]{160,360}={0,2})",
            source,
        ):
            try:
                padding = "=" * (-len(candidate) % 4)
                key = RSA.import_key(base64.b64decode(candidate + padding))
            except (ValueError, TypeError, IndexError):
                continue
            if key.size_in_bits() >= 1024:
                return candidate
        return ""

    @staticmethod
    def _iap_ajax_headers(
        context: IapLoginContext,
        *,
        device_id: str = "",
        fingerprint_id: str = "",
    ) -> dict[str, str]:
        headers = {
            "Content-Type": "application/x-www-form-urlencoded",
            "Origin": context.auth_host.rstrip("/"),
            "Referer": context.page_url,
            "X-Requested-With": "XMLHttpRequest",
        }
        if device_id:
            headers["deviceId"] = device_id
        if fingerprint_id:
            headers["fingerprintId"] = fingerprint_id
        return headers

    def _follow_iap_redirect(self, jump_url: str) -> None:
        response = self.http.get(jump_url, allow_redirects=True)
        if response.status_code == 405:
            response = self.http.post(jump_url, allow_redirects=True)
        if response.status_code >= 400:
            raise LoginError(
                f"IAP 服务票据跳转失败：HTTP {response.status_code}"
            )

    def _login_cas(
        self,
        username: str,
        password: str,
        login_url: str,
    ) -> None:
        """执行 CAS/authserver 表单登录。"""
        for attempt in range(1, 4):
            response = self.http.get(login_url, allow_redirects=True)
            parser = FormParser()
            parser.feed(response.text)
            form = self._choose_login_form(parser.forms)
            if form is None:
                raise LoginError("认证页面中没有找到密码登录表单")
            params: dict[str, str] = {}
            salt = ""
            for item in form.inputs:
                name = item.get("name", "")
                item_type = item.get("type", "text").lower()
                if not name or item_type in {
                    "button",
                    "checkbox",
                    "file",
                    "image",
                    "radio",
                    "reset",
                    "submit",
                }:
                    continue
                params[name] = item.get("value", "")
                if "encryptsalt" in name.lower():
                    salt = item.get("value", "")
            if not salt:
                match = re.search(
                    r"(?:pwdDefaultEncryptSalt|EncryptSalt)"
                    r"\s*=\s*['\"]([^'\"]+)['\"]",
                    response.text,
                    re.I,
                )
                if match:
                    salt = match.group(1)
            params["username"] = username
            params["password"] = (
                encrypt_cas_password(password, salt) if salt else password
            )
            form_id = form.form_id.lower()
            if self._cas_needs_captcha(response.url, username, form_id):
                raise LoginError(
                    "当前学校统一认证要求图形验证码或滑块验证，"
                    "本脚本不提供验证码识别或绕过。"
                    "请先在学校官方认证页面完成验证后再重试。"
                )
            rsa_match = re.search(
                r"RSAKeyPair\(\s*['\"]([^'\"]*)['\"]\s*,"
                r"\s*['\"]([^'\"]+)['\"]\s*,\s*['\"]([^'\"]+)['\"]",
                response.text,
                re.I,
            )
            if rsa_match and not salt:
                params["password"] = generate_legacy_rsa_password(
                    password,
                    rsa_match.group(3),
                    rsa_match.group(2),
                )
            submit_url = urljoin(response.url, form.action or response.url)
            login_response = self.http.post(
                submit_url,
                data=params,
                allow_redirects=False,
                headers={
                    "Content-Type": "application/x-www-form-urlencoded",
                },
            )
            location = login_response.headers.get("Location")
            if login_response.is_redirect and location:
                self.http.get(
                    urljoin(submit_url, location),
                    allow_redirects=True,
                )
                return
            if login_response.status_code in (200, 201):
                error = self._extract_error(login_response.text)
                if self._is_captcha_error(error or login_response.text):
                    if attempt < 3:
                        print(f"登录验证码未通过，正在刷新（{attempt + 1}/3）。")
                        continue
                    raise LoginError("统一认证验证码多次不匹配")
                raise LoginError(
                    error or "统一认证返回登录页，用户名或密码可能不正确"
                )
            raise LoginError(
                f"统一认证登录失败：HTTP {login_response.status_code}"
            )
        raise LoginError("统一认证登录失败")

    @staticmethod
    def _choose_login_form(
        forms: list[ParsedForm],
    ) -> ParsedForm | None:
        """选择包含密码字段的登录表单。"""
        for form in forms:
            if any(
                item.get("type", "").lower() == "password"
                for item in form.inputs
            ):
                return form
            if any(
                "password" in item.get("name", "").lower()
                for item in form.inputs
            ):
                return form
        return None

    def _cas_needs_captcha(
        self,
        login_url: str,
        username: str,
        form_id: str,
    ) -> bool:
        """探测 CAS/authserver 是否要求验证码。

        探测失败时返回 False，让服务端登录响应作为最终判断依据。
        """
        parsed = urlparse(login_url)
        if not parsed.scheme or not parsed.netloc:
            return False
        host = f"{parsed.scheme}://{parsed.netloc}/"
        try:
            if form_id == "casloginform":
                check = self.http.get(
                    urljoin(host, "authserver/needCaptcha.html"),
                    params={"username": username},
                )
                if check.status_code >= 400:
                    return False
                text = check.text.strip().casefold()
                if text in {"false", "0", "no", "否"}:
                    return False
                if text in {"true", "1", "yes", "是"}:
                    return True
                try:
                    body = check.json()
                except ValueError:
                    return "false" not in text
                value = self._find_first(
                    body,
                    {"isNeed", "needCaptcha", "validation"},
                )
                return self._as_bool(value)

            check = self.http.get(
                urljoin(host, "authserver/checkNeedCaptcha.htl"),
                params={"username": username},
            )
            if check.status_code >= 400:
                return False
            try:
                body = check.json()
            except ValueError:
                return self._as_bool(check.text)
            value = self._find_first(
                body,
                {"isNeed", "needCaptcha", "validation"},
            )
            return self._as_bool(value)
        except (CampusError, requests.RequestException, ValueError, TypeError):
            return False

    @staticmethod
    def _find_first(node: Any, names: set[str]) -> Any:
        """递归查找接口响应中的字段，字段名不区分大小写。"""
        lowered = {name.casefold() for name in names}
        if isinstance(node, dict):
            for key, value in node.items():
                if str(key).casefold() in lowered:
                    return value
            for value in node.values():
                found = PasswordAuthService._find_first(value, names)
                if found is not None:
                    return found
        elif isinstance(node, list):
            for value in node:
                found = PasswordAuthService._find_first(value, names)
                if found is not None:
                    return found
        return None

    @staticmethod
    def _as_bool(value: Any) -> bool:
        """兼容接口中的布尔值、数字、文本和嵌套对象。"""
        if isinstance(value, dict):
            nested = PasswordAuthService._find_first(
                value,
                {"success", "isSuccess", "needCaptcha", "isNeed", "value"},
            )
            return PasswordAuthService._as_bool(nested)
        if isinstance(value, bool):
            return value
        if isinstance(value, (int, float)):
            return value != 0
        normalized = str(value or "").strip().casefold()
        return normalized in {
            "1",
            "true",
            "yes",
            "success",
            "ok",
            "need",
            "needed",
            "需要",
            "是",
        }

    @staticmethod
    def _is_captcha_error(value: str) -> bool:
        """识别服务端返回的验证码或滑块验证错误。"""
        lowered = str(value or "").casefold()
        return any(
            word in lowered
            for word in (
                "captcha",
                "验证码",
                "校验码",
                "滑块",
                "行为验证",
            )
        )

    @staticmethod
    def _extract_error(html: str) -> str:
        """提取认证页面中常见的错误提示，并清理 HTML 标签。"""
        for pattern in (
            r'id=["\']errorMsg["\'][^>]*>(.*?)<',
            r'id=["\']msg["\'][^>]*>(.*?)<',
            r'class=["\'][^"\']*authError[^"\']*["\'][^>]*>(.*?)<',
            r'id=["\']formErrorTip2["\'][^>]*>(.*?)<',
            r'id=["\']showErrorTip["\'][^>]*>(.*?)<',
        ):
            match = re.search(pattern, html, re.I | re.S)
            if match:
                text = re.sub(r"<[^>]+>", "", match.group(1))
                return re.sub(r"\s+", " ", text).strip()
        return ""



# ---------------------------------------------------------------------------
# 原生短信验证码登录
# ---------------------------------------------------------------------------


NATIVE_API_HOST_CANDIDATES = (
    "https://data-xxt.aichaoxing.com/",
    "https://mobile.campushoy.com/",
)
INDIVI_LOGIN_PAGE = (
    "https://indivi.campushoy.com/appconfig/indivi//guest/loginpage"
)
SECRET_PATH = "app/auth/dynamic/secret/getSecretKey/v-920"
SMS_PATH = "app/auth/authentication/mobile/messageCode/v-8222"
LOGIN_PATH = "app/auth/authentication/mobileLogin/v-8222"
SECRET_SALT = (
    "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"
)
LOCAL_SECRET_PREFIX = "f9akfyUe"
DES_KEY = b"XCE927=="
DES_IV = bytes(range(1, 9))
AES_IV = bytes(
    (1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7)
)


class NativeCrypto:
    """封装原生动态 RSA、AES、DES 算法。"""

    def __init__(self) -> None:
        self.public_key = RSA.import_key(NATIVE_PUBLIC_KEY_PEM)
        self.private_key = RSA.import_key(NATIVE_PRIVATE_KEY_PEM)

    @staticmethod
    def _b64decode(value: str) -> bytes:
        """严格解码 Base64。"""
        try:
            return base64.b64decode(
                "".join(str(value).split()),
                validate=True,
            )
        except (ValueError, TypeError) as exc:
            raise ProtocolError("原生登录 Base64 字段格式无效") from exc

    @staticmethod
    def _b64encode(value: bytes) -> str:
        """编码标准 Base64。"""
        return base64.b64encode(value).decode("ascii")

    def rsa_encrypt(self, value: str) -> str:
        """使用 PKCS#1 v1.5 加密动态协商字符串。"""
        return self._b64encode(
            PKCS1_v1_5.new(self.public_key).encrypt(
                value.encode("utf-8")
            )
        )

    def rsa_decrypt_text(self, value: str) -> str:
        """解密服务端 RSA 字段。"""
        sentinel = secrets.token_bytes(32)
        plain = PKCS1_v1_5.new(self.private_key).decrypt(
            self._b64decode(value),
            sentinel,
        )
        if plain == sentinel:
            raise ProtocolError("原生登录 RSA 响应解密失败")
        try:
            return plain.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ProtocolError("原生登录 RSA 响应不是 UTF-8 文本") from exc

    @staticmethod
    def aes_encrypt(value: bytes, key: bytes) -> str:
        """使用 AES-CBC-PKCS7 加密并输出 Base64。"""
        cipher = AES.new(key, AES.MODE_CBC, AES_IV)
        return base64.b64encode(
            cipher.encrypt(pad(value, AES.block_size))
        ).decode("ascii")

    @staticmethod
    def aes_decrypt(value: str, key: bytes) -> bytes:
        """解密 AES 字段并校验填充。"""
        try:
            encrypted = base64.b64decode(
                "".join(value.split()),
                validate=True,
            )
            plain = AES.new(key, AES.MODE_CBC, AES_IV).decrypt(encrypted)
            return unpad(plain, AES.block_size)
        except (ValueError, TypeError) as exc:
            raise ProtocolError("原生登录 AES 字段解密失败") from exc

    @staticmethod
    def des_encrypt(value: bytes) -> str:
        """使用 DES-CBC-PKCS5 生成会话头密文。"""
        cipher = DES.new(DES_KEY, DES.MODE_CBC, DES_IV)
        return base64.b64encode(
            cipher.encrypt(pad(value, DES.block_size))
        ).decode("ascii")

    @staticmethod
    def derive_cpdaily_secret(raw_secret: str) -> str:
        """按原生客户端规则重排服务端密钥。"""
        value = LOCAL_SECRET_PREFIX + raw_secret
        return value[::2] + value[1::2]

    def decrypt_service_secret(self, value: str) -> NativeServiceSecret:
        """解密随机串、业务密钥和猫密钥。"""
        parts = self.rsa_decrypt_text(value).split("|")
        if len(parts) < 3 or any(not item for item in parts[:3]):
            raise ProtocolError("动态服务密钥响应段数不足")
        return NativeServiceSecret(
            random_string=parts[0],
            cpdaily_secret=self.derive_cpdaily_secret(parts[1]),
            cat_secret=parts[2],
        )


class NativeSmsAuthService:
    """执行原生短信验证码登录并应用当前会话。"""

    def __init__(self, http: HttpClient) -> None:
        self.http = http
        self.crypto = NativeCrypto()
        self._initial_token = ""
        self._secret: NativeServiceSecret | None = None
        self._login_page_code = ""
        self._session_headers: dict[str, str] = {}
        self._api_host = ""
        self._wis_device_id = http.device_id

    @staticmethod
    def _random_token() -> str:
        """生成原生格式的初始 SessionToken。"""
        return base64.b64encode(secrets.token_bytes(8)).decode("ascii")

    def _clear_stale_auth_state(self) -> None:
        """清理当前内存会话中的旧认证字段。"""
        auth_cookie_names = {
            "tgc",
            "sessiontoken",
            "sessiontokenkey",
            "ampcookies",
            "authorization",
            "accesstoken",
            "jsessionid",
        }
        jar = self.http.session.cookies
        for cookie in list(jar):
            normalized = "".join(
                char for char in str(cookie.name).casefold()
                if char.isalnum()
            )
            if normalized not in auth_cookie_names:
                continue
            try:
                jar.clear(cookie.domain, cookie.path, cookie.name)
            except KeyError:
                continue
        for header in (
            "TGC",
            "SessionToken",
            "SessionTokenKey",
            "AmpCookies",
            "Authorization",
        ):
            self.http.session.headers.pop(header, None)
        self._session_headers.clear()

    def reset_login_round(self) -> None:
        """清空上一轮短信登录的动态材料。"""
        self._secret = None
        self._initial_token = ""
        self._login_page_code = ""
        self._api_host = ""
        self._clear_stale_auth_state()

    @staticmethod
    def _response_data(body: dict[str, Any]) -> Any:
        """递归兼容 data、datas、result 包裹。"""
        current: Any = body
        for _ in range(6):
            if not isinstance(current, dict):
                return current
            for key in ("data", "datas", "result"):
                if key not in current:
                    continue
                candidate = current[key]
                if isinstance(candidate, dict):
                    current = candidate
                    break
                return candidate
            else:
                return current
        return current

    @staticmethod
    def _origin(value: str) -> str:
        """只保留协议和主机。"""
        parsed = urlparse(value.strip())
        if not parsed.scheme or not parsed.netloc:
            return ""
        return f"{parsed.scheme}://{parsed.netloc}/"

    def _api_host_candidates(self) -> list[str]:
        """生成去重后的原生接口主机候选。"""
        result: list[str] = []
        for value in (self._api_host, *NATIVE_API_HOST_CANDIDATES):
            host = self._origin(value)
            if host and host not in result:
                result.append(host)
        return result

    @staticmethod
    def _find_field(value: object, aliases: set[str]) -> str:
        """递归读取响应字段，兼容大小写和下划线差异。"""
        normalized_aliases = {
            "".join(
                char for char in str(alias).casefold()
                if char.isalnum()
            )
            for alias in aliases
        }
        if isinstance(value, dict):
            for key, item in value.items():
                normalized_key = "".join(
                    char for char in str(key).casefold()
                    if char.isalnum()
                )
                if normalized_key in normalized_aliases and item not in (
                    None,
                    "",
                ):
                    return str(item)
            for item in value.values():
                found = NativeSmsAuthService._find_field(item, aliases)
                if found:
                    return found
        elif isinstance(value, list):
            for item in value:
                found = NativeSmsAuthService._find_field(item, aliases)
                if found:
                    return found
        return ""

    def _cookie_value(self, aliases: set[str]) -> str:
        """读取会话 Cookie。"""
        normalized_aliases = {
            "".join(
                char for char in str(alias).casefold()
                if char.isalnum()
            )
            for alias in aliases
        }
        for cookie in self.http.session.cookies:
            normalized_name = "".join(
                char for char in str(cookie.name).casefold()
                if char.isalnum()
            )
            if normalized_name in normalized_aliases and cookie.value:
                return str(cookie.value)
        return ""

    def _response_header_value(self, aliases: set[str]) -> str:
        """读取最近一次响应头中的会话值。"""
        response = self.http.last_response
        if response is None:
            return ""
        normalized_aliases = {
            "".join(
                char for char in str(alias).casefold()
                if char.isalnum()
            )
            for alias in aliases
        }
        for name, value in response.headers.items():
            normalized_name = "".join(
                char for char in str(name).casefold()
                if char.isalnum()
            )
            if normalized_name in normalized_aliases and value:
                return str(value)
        return ""

    @staticmethod
    def _success_code(value: object) -> bool:
        """识别原生接口成功状态码。"""
        return value in (None, "", 0, 200, "0", "200", "SUCCESS", "success")

    @classmethod
    def _ensure_response_success(
        cls,
        response: dict[str, Any],
        action: str,
        *,
        require_nested_status: bool = False,
    ) -> None:
        """校验外层状态和短信发送接口的内层状态。"""
        outer_code = response.get(
            "errCode",
            response.get("code", response.get("resultCode")),
        )
        if not cls._success_code(outer_code):
            message = cls._find_field(
                response,
                {"errMsg", "message", "msg", "tipMsg", "description"},
            )
            suffix = f"：{message[:120]}" if message else ""
            raise LoginError(f"{action}失败{suffix}")
        if not require_nested_status:
            return
        data = cls._response_data(response)
        if not isinstance(data, dict):
            raise LoginError(f"{action}失败：响应缺少状态对象")
        status = cls._find_field(data, {"status", "code"})
        if status and not cls._success_code(status):
            message = cls._find_field(
                data,
                {"tipMsg", "message", "msg", "errMsg", "description"},
            )
            suffix = f"：{message[:120]}" if message else ""
            raise LoginError(f"{action}失败{suffix}")

    @classmethod
    def _is_unregistered_or_unbound(cls, profile: dict[str, Any]) -> bool:
        """判断手机号是否处于未注册或未绑定学校状态。"""
        status = cls._find_field(profile, {"status"})
        auth_status = cls._find_field(
            profile,
            {"authStatus", "auth_status"},
        )
        return (
            status.strip().casefold() == "schoolnologin"
            and auth_status.strip().casefold()
            in {"noauth", "unauth", "unauthenticated", "false", "0"}
        )

    @classmethod
    def _incomplete_session_message(cls, profile: dict[str, Any]) -> str:
        """将未建立会话的状态转换为简短中文提示。"""
        if cls._is_unregistered_or_unbound(profile):
            return "账号未注册或未绑定学校"
        auth_status = cls._find_field(
            profile,
            {"authStatus", "auth_status"},
        )
        if auth_status.strip().casefold() in {
            "noauth",
            "unauth",
            "unauthenticated",
            "false",
            "0",
        }:
            return "账号未注册或未绑定学校"
        return "短信验证码登录未建立会话"

    def _device_info(self) -> dict[str, Any]:
        """生成原生请求头中的设备对象。"""
        return {
            "deviceId": self.http.device_id,
            "systemName": "android",
            "appVersion": self.http.app_version,
            "model": self.http.model,
            "lon": 0,
            "lat": 0,
            "cpdailyVersion": self.http.app_version,
            "systemVersion": self.http.system_version,
            "userId": "",
        }

    def _cpdaily_info(self) -> str:
        """生成 DES 加密 CpdailyInfo 请求头。"""
        payload = json.dumps(
            self._device_info(),
            ensure_ascii=False,
            separators=(",", ":"),
        ).encode("utf-8")
        cipher = DES.new(DES_KEY, DES.MODE_CBC, DES_IV)
        return base64.b64encode(
            cipher.encrypt(pad(payload, DES.block_size))
        ).decode("ascii")

    def _build_headers(self, tenant_id: str = "") -> dict[str, str]:
        """构造每轮动态原生请求头。"""
        if not self._initial_token:
            self._initial_token = self._random_token()
        return {
            "CpdailyClientType": "CPDAILY",
            "CpdailyStandAlone": "0",
            "CpdailyInfo": self._cpdaily_info(),
            "tenantId": tenant_id,
            "clientType": "cpdaily_student",
            "deviceType": "1",
            "SessionTokenKey": self._initial_token,
            "SessionToken": self._initial_token,
            "wisDeviceId": self._wis_device_id,
        }

    def negotiate_secret(self, tenant_id: str = "") -> NativeServiceSecret:
        """协商本轮动态服务密钥。"""
        if self._secret is None and not self._initial_token:
            self._clear_stale_auth_state()
        private_data = f"{uuid.uuid4()}|first_v4"
        payload = {
            "p": self.crypto.rsa_encrypt(private_data),
            "s": hashlib.md5(
                f"{private_data}&{SECRET_SALT}".encode("utf-8")
            ).hexdigest(),
        }
        errors: list[str] = []
        for host in self._api_host_candidates():
            try:
                response = self.http.post_json(
                    f"{host}{SECRET_PATH}",
                    payload,
                    headers=self._build_headers(tenant_id),
                )
                self._ensure_response_success(response, "动态密钥协商")
                data = self._response_data(response)
                if not isinstance(data, str) or not data:
                    errors.append(f"{urlparse(host).netloc}:empty")
                    continue
                self._secret = self.crypto.decrypt_service_secret(data)
                self._api_host = host
                return self._secret
            except Exception as exc:
                errors.append(
                    f"{urlparse(host).netloc}:{type(exc).__name__}"
                )
        raise LoginError(
            "动态密钥协商失败：" + "、".join(errors)
        )

    def load_login_page_code(self) -> str:
        """读取原生登录页配置。"""
        response = self.http.get(INDIVI_LOGIN_PAGE)
        if response.status_code >= 400:
            raise LoginError("原生登录页配置读取失败")
        try:
            body = response.json()
        except ValueError as exc:
            raise ProtocolError("原生登录页配置不是 JSON") from exc
        code = body.get("sc")
        if not isinstance(code, str) and isinstance(body.get("data"), dict):
            code = body["data"].get("sc")
        self._login_page_code = str(code or "")
        return self._login_page_code

    def send_sms_code(
        self,
        phone: str,
        tenant_id: str = "",
    ) -> dict[str, Any]:
        """加密手机号并发送短信验证码。"""
        if self._secret is None:
            self.negotiate_secret(tenant_id)
        assert self._secret is not None
        payload = {
            "a": self.crypto.aes_encrypt(
                phone.strip().encode("utf-8"),
                self._secret.cpdaily_secret.encode("utf-8"),
            ),
            "b": "first_v4",
        }
        response = self.http.post_json(
            f"{self._api_host}{SMS_PATH}",
            payload,
            headers=self._build_headers(tenant_id),
        )
        self._ensure_response_success(
            response,
            "短信验证码发送",
            require_nested_status=True,
        )
        return response

    def start_login_round(
        self,
        phone: str,
        tenant_id: str = "",
    ) -> dict[str, Any]:
        """创建新动态密钥轮次并发送短信。"""
        self.reset_login_round()
        self.negotiate_secret(tenant_id)
        self.load_login_page_code()
        return self.send_sms_code(phone, tenant_id)

    def login_with_sms(
        self,
        phone: str,
        code: str,
        tenant_id: str = "",
    ) -> NativeLoginResult:
        """加密手机号和短信码，完成原生登录。"""
        if self._secret is None:
            self.negotiate_secret(tenant_id)
        assert self._secret is not None
        if not self._login_page_code:
            self.load_login_page_code()
        login_data = {
            "c": phone.strip(),
            "d": code.strip(),
            "e": "CPDAILY",
            "f": "86",
        }
        payload = {
            "a": self.crypto.aes_encrypt(
                json.dumps(
                    login_data,
                    ensure_ascii=False,
                    separators=(",", ":"),
                ).encode("utf-8"),
                self._secret.cpdaily_secret.encode("utf-8"),
            ),
            "b": "first_v4",
        }
        response = self.http.post_json(
            f"{self._api_host}{LOGIN_PATH}",
            payload,
            headers=self._build_headers(tenant_id),
        )
        self._ensure_response_success(response, "短信验证码登录")
        data = self._response_data(response)
        if not isinstance(data, str) or not data:
            raise LoginError("短信验证码登录失败")
        try:
            profile = json.loads(
                self.crypto.aes_decrypt(
                    data,
                    self._secret.cpdaily_secret.encode("utf-8"),
                ).decode("utf-8")
            )
        except (ValueError, TypeError, UnicodeDecodeError) as exc:
            raise ProtocolError("短信验证码登录响应解密或解析失败") from exc
        if not isinstance(profile, dict):
            raise ProtocolError("短信验证码登录响应不是对象")

        if self._is_unregistered_or_unbound(profile):
            raise LoginError("账号未注册或未绑定学校")

        result = NativeLoginResult(
            tenant_id=self._find_field(
                profile,
                {"tenantId", "tenant_id"},
            ),
            tenant_name=self._find_field(
                profile,
                {"tenantName", "tenant_name"},
            ),
            mobile=self._find_field(
                profile,
                {"mobile", "phone"},
            ) or phone,
            device_status=self._find_field(
                profile,
                {"deviceStatus", "device_status"},
            ),
            session_token=self._find_field(
                profile,
                {"sessionToken", "session_token", "sessiontoken"},
            )
            or self._cookie_value({"sessionToken", "sessiontoken"})
            or self._response_header_value(
                {"sessionToken", "sessiontoken", "xSessionToken"}
            ),
            tgc=(
                self._find_field(profile, {"tgc", "TGC", "castgc"})
                or self._cookie_value({"tgc", "castgc"})
                or self._response_header_value(
                    {"tgc", "castgc", "xTgc"}
                )
            ),
            profile=profile,
        )
        if not result.session_token or not result.tgc:
            raise LoginError(self._incomplete_session_message(profile))
        self._apply_session(result)
        return result

    def _apply_session(self, result: NativeLoginResult) -> None:
        """把登录返回的会话字段转换成业务请求头和 Cookie。"""
        encrypted_session = self.crypto.des_encrypt(
            result.session_token.encode("utf-8")
        )
        encrypted_tgc = self.crypto.des_encrypt(
            result.tgc.encode("utf-8")
        )
        amp_session = {
            "value": result.session_token,
            "name": "sessionToken",
        }
        amp_payload = json.dumps(
            {
                "AMP1": [amp_session],
                "AMP2": [amp_session],
            },
            ensure_ascii=False,
            separators=(",", ":"),
        ).encode("utf-8")
        encrypted_amp = self.crypto.des_encrypt(amp_payload)
        self._session_headers = {
            "SessionTokenKey": encrypted_session,
            "SessionToken": encrypted_session,
            "TGC": encrypted_tgc,
            "AmpCookies": encrypted_amp,
            "tenantId": result.tenant_id,
        }
        self.http.session.headers.update(self._session_headers)
        cookie_domain = ".campushoy.com"
        for name, value in (
            ("clientType", "cpdaily_student"),
            ("tenantId", result.tenant_id),
            ("standAlone", "0"),
            ("sessionToken", result.session_token),
            ("TGC", result.tgc),
        ):
            self.http.session.cookies.set(
                name,
                value,
                domain=cookie_domain,
                path="/",
            )
        self.http.session.cookies.set(
            "SessionToken",
            result.session_token,
            domain="mobile.campushoy.com",
            path="/",
        )

    @property
    def api_host(self) -> str:
        """返回当前轮次成功使用的原生主机。"""
        return self._api_host

    @property
    def session_headers(self) -> dict[str, str]:
        """返回当前会话头副本。"""
        return dict(self._session_headers)


# ---------------------------------------------------------------------------
# 账号信息只读接口
# ---------------------------------------------------------------------------


class AccountInfoService:
    """登录成功后读取当前账号信息。"""

    NATIVE_PROFILE_PATH = "v6/user/new/myMainPage"
    NATIVE_PROFILE_HOSTS = (
        "https://data-xxt.aichaoxing.com/",
        "https://mobile.campushoy.com/",
    )
    DEFAULT_ENDPOINTS = (
        "wec-counselor-stuinfo-apps/student/detail/getStuMainMustInfos",
        "wec-im-group/group/groupMember/getCurrentUserId",
        "wec-portal-mobile/client/user/getUserInfo",
        "wec-portal-mobile/client/user/queryUserInfo",
        "wec-portal-mobile/client/user/getUserBaseInfo",
        "wec-portal-mobile/client/account/getUserInfo",
        "wec-counselor-sign-apps/stu/sign/getStuInfo",
    )

    def __init__(self, http: HttpClient) -> None:
        self.http = http

    def get_current(
        self,
        username: str,
        tenant: Tenant | None = None,
    ) -> dict[str, Any]:
        """按原生资料接口、学校只读接口顺序读取账号信息。"""
        attempts: list[dict[str, Any]] = []
        for host in self.NATIVE_PROFILE_HOSTS:
            try:
                raw = self.http.post(
                    f"{host}{self.NATIVE_PROFILE_PATH}",
                    data=b"",
                )
                if raw.status_code >= 400:
                    attempts.append(
                        {
                            "endpoint": self.NATIVE_PROFILE_PATH,
                            "host": host,
                            "status": f"http={raw.status_code}",
                        }
                    )
                    continue
                body = raw.json()
                if not isinstance(body, dict):
                    raise ProtocolError("原生资料接口根节点不是对象")
                if not self._is_native_success(body):
                    attempts.append(
                        {
                            "endpoint": self.NATIVE_PROFILE_PATH,
                            "host": host,
                            "status": self._response_status(body),
                        }
                    )
                    continue
                data = self.http.data_of(body)
                if isinstance(data, dict) and data:
                    return {
                        "source": "native-mobile-profile",
                        "endpoint": self.NATIVE_PROFILE_PATH,
                        "username": username,
                        "profile": data,
                    }
            except Exception as exc:
                attempts.append(
                    {
                        "endpoint": self.NATIVE_PROFILE_PATH,
                        "host": host,
                        "error": type(exc).__name__,
                    }
                )

        for endpoint in self.DEFAULT_ENDPOINTS:
            for method in ("POST", "GET"):
                try:
                    if method == "POST":
                        body = self.http.post_json(
                            endpoint,
                            {},
                            headers=self._school_profile_headers(),
                            check_http=False,
                        )
                    else:
                        raw = self.http.get(
                            endpoint,
                            headers=self._school_profile_headers(),
                        )
                        if raw.status_code >= 400:
                            continue
                        body = raw.json()
                    data = self.http.data_of(body)
                    profile = self._profile_object(data)
                    if profile and not self._is_unauthenticated(profile):
                        return {
                            "source": endpoint,
                            "method": method,
                            "username": username,
                            "profile": self._normalize_profile(profile),
                        }
                    attempts.append(
                        {
                            "endpoint": endpoint,
                            "method": method,
                            "status": (
                                "unauthenticated"
                                if profile
                                and self._is_unauthenticated(profile)
                                else "empty"
                            ),
                        }
                    )
                except Exception as exc:
                    attempts.append(
                        {
                            "endpoint": endpoint,
                            "method": method,
                            "error": type(exc).__name__,
                        }
                    )

        unauthenticated = [
            item
            for item in attempts
            if item.get("status") == "unauthenticated"
        ]
        result: dict[str, Any] = {
            "source": "local-session",
            "username": username,
            "cookies": sorted(
                cookie.name for cookie in self.http.session.cookies
            ),
            "probe_attempts": attempts,
        }
        if unauthenticated:
            result["warning"] = (
                "统一认证已通过，但应用侧会话未建立：所有学校资料接口均"
                "返回未登录占位响应，可能是 portal 入口未激活或该学校"
                "需要额外的应用授权。"
            )
        if tenant is not None:
            result["school"] = tenant.to_dict()
        return result

    def _school_profile_headers(self) -> dict[str, str]:
        """构造与学校 H5 资料页相同的只读 AJAX 请求头。"""
        origin = str(self.http.host or "").rstrip("/")
        headers = {
            "Accept": "application/json, text/plain, */*",
            "X-Requested-With": "XMLHttpRequest",
        }
        if origin:
            headers["Origin"] = origin
            headers["Referer"] = f"{origin}/"
        return headers

    @staticmethod
    def _is_unauthenticated(profile: dict[str, Any]) -> bool:
        """识别服务端返回的“未登录/需要跳转登录”占位响应。

        典型形态：{"WEC-HASLOGIN": false, "WEC-REDIRECTURL": "/portal/login"}，
        这类非空字典曾被误判为有效资料，需要单独拦截。
        """
        if not any(
            str(key).upper().startswith("WEC-") for key in profile
        ):
            return False
        has_login = profile.get("WEC-HASLOGIN")
        if isinstance(has_login, bool) and not has_login:
            return True
        redirect = profile.get("WEC-REDIRECTURL")
        if isinstance(redirect, str) and redirect:
            return True
        return all(not value for value in profile.values())

    @staticmethod
    def _profile_object(data: Any) -> dict[str, Any]:
        """兼容资料接口返回对象或仅包含当前学生的一项列表。"""
        if isinstance(data, dict) and data:
            return data
        if isinstance(data, list):
            for item in data:
                if isinstance(item, dict) and item:
                    return item
        return {}

    @staticmethod
    def _normalize_profile(profile: dict[str, Any]) -> dict[str, Any]:
        """补充统一字段名，同时保留学校接口的原始字段。"""
        result = dict(profile)
        aliases = {
            "name": ("name", "userName"),
            "student_no": ("studentNo", "studentId", "xh"),
            "user_id": ("userId", "userWid", "personId", "openId"),
            "academy": ("academy", "department", "dwmc"),
            "major": ("major", "zymc"),
            "class_name": ("className", "bjmc"),
            "grade": ("grade", "nj"),
            "mobile": ("mobile", "mobilePhone", "phone"),
            "school_zone": ("schoolZone", "campusName"),
        }
        for normalized, candidates in aliases.items():
            if result.get(normalized) not in (None, ""):
                continue
            for candidate in candidates:
                value = profile.get(candidate)
                if value not in (None, ""):
                    result[normalized] = value
                    break
        return result

    @staticmethod
    def _is_native_success(body: dict[str, Any]) -> bool:
        """识别原生资料接口的成功语义。"""
        code = body.get("errCode")
        if code not in (None, 0, "0", "200", 200):
            return False
        data = body.get(
            "data",
            body.get("datas", body.get("result")),
        )
        return isinstance(data, dict) and bool(data)

    @staticmethod
    def _response_status(body: dict[str, Any]) -> str:
        """生成简短状态摘要。"""
        for key in ("errCode", "code", "status", "resultCode"):
            if key in body:
                return f"{key}={body[key]}"
        return "empty"


# ---------------------------------------------------------------------------
# 交互式入口
# ---------------------------------------------------------------------------


class InteractiveLoginApp:
    """提供密码登录、短信登录和账号信息输出。"""

    def __init__(self) -> None:
        self.http = HttpClient()
        self.tenants = TenantService(self.http)
        self.password_auth = PasswordAuthService(self.http)
        self.native_auth = NativeSmsAuthService(self.http)
        self.account_info = AccountInfoService(self.http)

    def run(self) -> None:
        """运行交互式菜单。"""
        print("=" * 58)
        print("今日校园登录")
        print("本脚本只执行登录和信息读取，不执行打卡、补签、日报或其他操作")
        print("本脚本不识别或绕过图形验证码；触发验证码时将停止登录")
        print("=" * 58)
        while True:
            print("\n请选择：")
            print("1. 学校账号密码登录并获取信息")
            print("2. 手机短信验证码登录并获取信息")
            print("0. 退出")
            choice = input("请输入序号：").strip().lower()
            try:
                if choice == "1":
                    self._password_flow()
                elif choice == "2":
                    self._sms_flow()
                elif choice == "0":
                    print("已退出。")
                    return
                else:
                    print("请输入 1、2 或 0。")
            except KeyboardInterrupt:
                print("\n已取消。")
                return
            except (CampusError, requests.RequestException) as exc:
                print(f"操作失败：{exc}")
            except Exception as exc:
                print(f"操作失败：{type(exc).__name__}：{exc}")

    def _password_flow(self) -> None:
        """执行学校统一认证账号密码登录。"""
        from getpass import getpass

        account_input = input(
            "请输入账号（支持 学校名称::账号、学校域名\\账号或校园邮箱）："
        ).strip()
        if not account_input:
            print("账号不能为空。")
            return
        school, identity = self._resolve_school(account_input)
        password = getpass("请输入密码：")
        if not password:
            print("密码不能为空。")
            return
        if not school.login_url:
            raise LoginError("学校没有可用的统一认证入口")
        self.http.set_host(school.host)
        self.password_auth.login(
            identity.login_name,
            password,
            school.login_url,
        )
        activation = self.http.activate_portal_session()
        status = activation.get("status")
        if not activation.get("attempted") or (
            isinstance(status, int) and status >= 400
        ):
            print("提示：未能成功激活应用会话，资料接口可能仍返回未登录。")
        result = self.account_info.get_current(
            identity.login_name,
            school,
        )
        self._print_result(result)

    def _sms_flow(self) -> None:
        """执行短信验证码登录并获取账号信息。"""
        phone = input("请输入手机号：").strip()
        if not phone:
            print("手机号不能为空。")
            return
        tenant_id = ""
        try:
            self.native_auth.start_login_round(phone, tenant_id)
            print("短信验证码已发送。")
        except LoginError as exc:
            print(f"操作失败：{exc}")
            return

        while True:
            code = input("短信验证码（输入 q 取消）：").strip()
            if code.casefold() == "q":
                return
            if not code:
                print("验证码不能为空。")
                continue
            try:
                result = self.native_auth.login_with_sms(
                    phone,
                    code,
                    tenant_id,
                )
                tenant = Tenant(
                    tenant_id=result.tenant_id,
                    name=result.tenant_name,
                    join_type="NATIVE_SMS",
                )
                result_info = self.account_info.get_current(phone, tenant)
                self._print_result(result_info)
                return
            except LoginError as exc:
                message = str(exc)
                if message == "账号未注册或未绑定学校":
                    print(message)
                    return
                print(f"验证码登录未完成：{message}")
                action = input(
                    "继续输入验证码重试；输入 r 重新发送短信；输入 q 取消："
                ).strip().lower()
                if action == "q":
                    return
                if action == "r":
                    try:
                        self.native_auth.start_login_round(phone, tenant_id)
                        print("短信验证码已重新发送。")
                    except LoginError as resend_error:
                        print(f"操作失败：{resend_error}")
                        return
            except CampusError as exc:
                print(f"验证码登录未完成：{exc}")

    def _resolve_school(
        self,
        account_input: str,
    ) -> tuple[Tenant, AccountIdentity]:
        """优先自动识别学校，失败时用学校关键词完成交互式选择。"""
        try:
            tenant, identity = self.tenants.detect_from_account(
                account_input
            )
        except ProtocolError:
            identity = parse_account_identity(account_input)
            keyword = input(
                "未能仅凭账号自动识别学校，请输入学校名称、租户代码或域名："
            ).strip()
            if not keyword:
                raise ProtocolError("学校线索不能为空")
            matches = self.tenants.search(keyword)
            if not matches:
                raise ProtocolError("没有匹配到学校")
            if len(matches) > 1:
                print("匹配到以下学校：")
                for index, item in enumerate(matches[:20], 1):
                    print(f"{index}. {item.name}（{item.tenant_id}）")
                raw_index = input("请选择学校序号：").strip()
                try:
                    selected = int(raw_index)
                    tenant = matches[selected - 1]
                except (ValueError, IndexError) as exc:
                    raise ProtocolError("学校序号无效") from exc
            else:
                tenant = matches[0]
        tenant = self.tenants.load_info(tenant)
        return tenant, identity

    @staticmethod
    def _print_result(result: dict[str, Any]) -> None:
        """格式化输出账号信息。"""
        print("\n登录成功，当前账号信息如下：")
        print(
            json.dumps(
                result,
                ensure_ascii=False,
                indent=2,
                default=str,
            )
        )


def main() -> None:
    """脚本主入口。"""
    InteractiveLoginApp().run()


if __name__ == "__main__":
    main()
