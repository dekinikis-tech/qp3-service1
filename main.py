#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
VPN Scout 2.0

Собирает публичные VLESS / Trojan / Shadowsocks конфиги, проверяет их через
xray и публикует результат (vps.txt, sub.txt, index.html) в GitHub Gist.

Зависимости: requests, geoip2 (опционально), бинарник xray в PATH.
"""
from __future__ import annotations

import base64
import concurrent.futures as cf
import contextlib
import functools
import html as html_lib
import ipaddress
import json
import os
import queue
import random
import re
import shutil
import socket
import ssl
import statistics
import subprocess
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request as url_req

import requests

# ============================================================
# НАСТРОЙКИ
# ============================================================
on, off = True, False

GID         = os.environ.get('MY_GIST_ID')
FILE_NAME   = "vps.txt"
SUB_FILE    = "sub.txt"
RU_FILE     = "vps_ru.txt"
RU_SUB_FILE = "sub_ru.txt"
VIEWER_FILE = "index.html"
XRAY_BIN    = os.environ.get('XRAY_BIN', 'xray')
TOP_N_EACH  = 900
GEOIP_DB_PATH = os.environ.get('GEOIP_DB', 'GeoLite2-Country.mmdb')

# --- Фильтры ---
FILTER_INSECURE    = on    # скрыть ⚠️ небезопасные (нет шифрования / allowInsecure=1)
FILTER_LOCK        = on   # скрыть 🔒 обычный TLS (оставить только Reality 🔑)
FILTER_RUSSIAN     = on   # скрыть 🇷🇺 российские серверы
FILTER_INVALID_PBK = on    # скрыть Reality с битым pbk/sid
FILTER_MITM        = on    # скрыть серверы, подменяющие HTTPS-сертификаты
REQUIRE_HTTPS      = on    # NEW: сервер обязан пройти HTTPS-проверку (как тест в v2rayNG);
                           # раньше хватало голого HTTP, и «полуживые» серверы попадали в список
NAME_SHOW_SECURITY = on    # NEW: иконка защиты в начале имени (🔑 Reality / 🔒 TLS / ⚠️)
NAME_NUMBERING     = on    # NEW: «Germany #1, #2…» (нумерация по пингу внутри группы)
WHITELIST_LABEL    = "Белые списки"
# «Белыми» считаются ТОЛЬКО файлы igareck с этой подстрокой в имени (WHITE-CIDR…, WHITE-SNI…).
# Сторонние агрегаторы (rjsxrd, vless-parser) намеренно НЕ учитываются: они тянут в свои
# «whitelist»-файлы почти всё подряд, включая обычные чёрные списки.
WHITELIST_SOURCE_MARKERS = ('white',)
PUBLISH_RU_FILES   = on    # NEW: отдельная подписка с российскими серверами (vps_ru.txt / sub_ru.txt)
# Проверка «жив ли сайт из SNI» с GitHub-раннера (США) даёт ложные отказы для
# российских SNI (vk.com, max.ru ...) — они гео-блокируют зарубежные IP.
# Для Reality клиент вообще не ходит на этот сайт, поэтому по умолчанию выключено.
FILTER_DEAD_SNI    = off
SNI_CHECK_TIMEOUT  = 4.0

CHECK_GOOGLE_BAN   = on    # отсеивать IP, которым Google отдаёт captcha (/sorry/)
BLOCK_CDN_BY_DNS   = off   # on = отбрасывать и домены, резолвящиеся в CDN-диапазоны
MAX_PER_ENDPOINT   = 3     # сколько вариантов конфига на один host:port оставлять

# --- Цепочка через российские серверы ---
CHAIN_PROXY = off
CHAIN_TOP_N = 8            # сколько лучших РФ-серверов брать как «входы»
CHAIN_TRIES = 2            # через сколько из них перепроверять каждый зарубежный

# --- Этап 1: TCP ---
TCP_WORKERS = 100
TCP_TIMEOUT = 1.5

# --- Этап 2: xray ---
_slow              = os.environ.get('MY_SLOW_NET') == '1'
XRAY_WORKERS       = 25
PING_ROUNDS        = 3
MAX_PING_MS        = 6000 if _slow else 4000
MAX_LOSS_RATE      = 0.67 if _slow else 0.5
REQUEST_TIMEOUT    = 12.0 if _slow else 7.0
XRAY_START_TIMEOUT = 5.0  if _slow else 3.5
XRAY_PORT_BASE     = 25000

TEST_URLS = [
    "http://www.instagram.com/",
    "http://www.facebook.com/",
    "http://www.gstatic.com/generate_204",
    "http://cp.cloudflare.com/",
]
# HTTPS с проверкой сертификата: ловит MITM и серверы, подсовывающие заглушки.
INTEGRITY_URL = "https://www.gstatic.com/generate_204"
OK_STATUS     = {200, 204, 301, 302, 308}

SUPPORTED_PROTOS = ('vless', 'trojan', 'ss')   # hysteria2 xray-ом не проверить

# ---------------------------------------------------------------------------
# ИСТОЧНИКИ (актуально на 26.10.2026)
# ---------------------------------------------------------------------------
_IGARECK        = "https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/refs/heads/main/"
_IGARECK_GITLAB = "https://gitlab.com/igareck/vpn-configs-for-russia/-/raw/main/"
_RJSXRD         = "https://raw.githubusercontent.com/whoahaow/rjsxrd/refs/heads/main/githubmirror/"
_COLORAMA       = "https://raw.githubusercontent.com/coloramamoe/vless-parser/main/githubmirror/"

# ЯДРО — igareck: списки проходят автотесты с сервера в РФ каждые ~2 часа.
# Живость проверена напрямую: BLACK_VLESS_RUS.txt (обновлён 23.10.2026),
# WHITE-CIDR-RU-checked.txt (11.10.2026). Остальные файлы — из прежнего списка.
SOURCES_CORE = [_IGARECK + f for f in (
    "BLACK_VLESS_RUS.txt",
    "BLACK_VLESS_RUS_mobile.txt",
    "BLACK_SS+All_RUS.txt",
    "WHITE-CIDR-RU-checked.txt",
    "WHITE-SNI-RU-all.txt",
    "Vless-Reality-White-Lists-Rus-Mobile.txt",
    "WHITE-CIDR-RU-all.txt",   # много почти-дублей; уберите, если не нужен
)]

# ДОПОЛНИТЕЛЬНЫЕ — сторонние агрегаторы под белые списки РФ. Это чужие,
# непроверяемые серверы: полагайтесь на FILTER_MITM и xray-проверку.
# Репозитории активны (rjsxrd обновляется ежечасно, ~800 звёзд); сами raw-пути
# взяты из их README и напрямую мной не открывались.
SOURCES_EXTRA = [
    _RJSXRD + "bypass/bypass-all.txt",              # SNI/CIDR bypass, до ~4500 конфигов
    _COLORAMA + "whitelist-vless.txt",              # только валидные reality/tls VLESS
    _COLORAMA + "ru-sni-best-vless.txt",            # reality с русским SNI
]

# ОПЦИОНАЛЬНО — общие (не РФ-ориентированные) подборки; по умолчанию выключены.
SOURCES_OPTIONAL = [
    # "https://raw.githubusercontent.com/0xRadikal/Free-v2ray-Configs/main/verified/configs.txt",
    # "https://raw.githubusercontent.com/ebrasha/free-v2ray-public-list/refs/heads/main/vless_configs.txt",
    # _RJSXRD + "split-by-protocols/vless-secure.txt",
]

USE_EXTRA_SOURCES    = on
USE_OPTIONAL_SOURCES = off
SOURCES = (SOURCES_CORE
           + (SOURCES_EXTRA if USE_EXTRA_SOURCES else [])
           + (SOURCES_OPTIONAL if USE_OPTIONAL_SOURCES else []))

# Зеркала на случай недоступности GitHub (актуально при запуске из РФ).
# Формат GitLab-raw стандартный, но конкретно эти ссылки я не открывал.
MIRRORS = {_IGARECK: _IGARECK_GITLAB}

BLACK_LIST = [
    'meshky', '4mohsen', 'white', '708087',
    'oneclick', '4jadi', '4kian', 'yandex.net', 'vk-apps.com',
]

# Точные диапазоны вместо префиксов вида '104.' (это был весь /8, а не Cloudflare).
BLOCKED_NETS = [ipaddress.ip_network(n) for n in (
    # Cloudflare
    '173.245.48.0/20', '103.21.244.0/22', '103.22.200.0/22', '103.31.4.0/22',
    '141.101.64.0/18', '108.162.192.0/18', '190.93.240.0/20', '188.114.96.0/20',
    '197.234.240.0/22', '198.41.128.0/17', '162.158.0.0/15', '104.16.0.0/13',
    '104.24.0.0/14', '172.64.0.0/13', '131.0.72.0/22', '162.159.0.0/16',
    # Yandex Cloud
    '51.250.0.0/16', '84.201.0.0/16', '158.160.0.0/16',
)]

PROTO_REGEX = re.compile(r'(?<![A-Za-z0-9])(?:vless|trojan|ss)://[^\s\'"<>]+')

AEAD_METHODS = {
    'aes-128-gcm', 'aes-256-gcm', 'chacha20-ietf-poly1305', 'chacha20-poly1305',
    'xchacha20-ietf-poly1305', '2022-blake3-aes-128-gcm',
    '2022-blake3-aes-256-gcm', '2022-blake3-chacha20-poly1305',
}


# ============================================================
# ПАРСИНГ ССЫЛОК
# ============================================================

def _b64decode(s: str) -> str | None:
    padded = s + '=' * ((-len(s)) % 4)
    for dec in (base64.urlsafe_b64decode, base64.b64decode):
        try:
            return dec(padded).decode('utf-8')
        except Exception:
            continue
    return None


def _parse_ss(url: str) -> dict | None:
    """SIP002 (ss://b64(method:pass)@host:port) и legacy (ss://b64(method:pass@host:port))."""
    body = url[len('ss://'):]
    tag = ''
    if '#' in body:
        body, tag = body.split('#', 1)
    query = ''
    if '@' in body:
        userinfo, hostport = body.rsplit('@', 1)
        if '?' in hostport:
            hostport, query = hostport.split('?', 1)
        hostport = hostport.split('/')[0]
        userinfo = urllib.parse.unquote(userinfo)
        if ':' not in userinfo:
            userinfo = _b64decode(userinfo) or ''
    else:
        decoded = _b64decode(body)
        if not decoded or '@' not in decoded:
            return None
        userinfo, hostport = decoded.rsplit('@', 1)
    if ':' not in userinfo or ':' not in hostport:
        return None
    method, password = userinfo.split(':', 1)
    host, _, port_s = hostport.rpartition(':')
    try:
        port = int(port_s)
    except ValueError:
        return None
    host = host.strip('[]')
    if not host or not (0 < port < 65536):
        return None
    return {
        'proto': 'ss', 'host': host, 'port': port, 'method': method.lower(),
        'password': password, 'q': {}, 'plugin': 'plugin=' in query.lower(),
        'tag': urllib.parse.unquote(tag),
    }


@functools.lru_cache(maxsize=None)
def parse_link(url: str) -> dict | None:
    """Единый разбор vless/trojan/ss. Результат нельзя изменять (кэшируется)."""
    try:
        if url.startswith(('vless://', 'trojan://')):
            u = urllib.parse.urlsplit(url)
            host, port = u.hostname, u.port
            if not host or not port or not u.username:
                return None
            q = {k: v[0] for k, v in urllib.parse.parse_qs(u.query).items()}
            return {
                'proto': u.scheme, 'host': host, 'port': port,
                'secret': urllib.parse.unquote(u.username), 'q': q,
                'plugin': False, 'tag': urllib.parse.unquote(u.fragment),
            }
        if url.startswith('ss://'):
            return _parse_ss(url)
    except ValueError:
        return None
    return None


# ============================================================
# ГЕОЛОКАЦИЯ
# ============================================================
_RESOLVED: dict = {}       # host -> IPv4 (заполняется на TCP-этапе)

RU_TAG_RE = re.compile(r'russia|russian|росси|(?<!\w)рф(?!\w)|\U0001f1f7\U0001f1fa', re.I)
RU_SNI_KEYWORDS = (
    'ozone.ru', 'vk.com', 'vk-apps', 'x5.ru', 'max.ru', 'firstvideocdn.ru',
    'eh.vk', 'mail.ru', 'yandex.', 'sber.', 'gosuslugi.', 'mos.ru', 'rmp-inc',
)
RU_TLDS = ('.ru', '.su', '.рф', '.xn--p1ai')
RU_DOMAIN_KEYWORDS = (
    'yandex', 'vk.com', 'vk-apps', 'mail.ru', 'selectel', 'beget',
    'reg.ru', 'timeweb', 'aeza.',
)

_geoip_reader = None


def _init_geoip():
    global _geoip_reader
    if _geoip_reader is not None:
        return
    try:
        import geoip2.database
        _geoip_reader = geoip2.database.Reader(GEOIP_DB_PATH)
        print(f"  GeoIP: база загружена из {GEOIP_DB_PATH}")
    except Exception as e:
        print(f"  GeoIP: не удалось загрузить базу ({e}) — только домен/тег")


def _geoip_is_russia(ip: str) -> bool | None:
    if _geoip_reader is None:
        return None
    try:
        return _geoip_reader.country(ip).country.iso_code == 'RU'
    except Exception:
        return None


def _is_ip_literal(host: str) -> bool:
    try:
        ipaddress.ip_address(host)
        return True
    except ValueError:
        return False


def _is_russian_server(host: str, url: str = '') -> bool:
    host = (host or '').lower()
    ip = host if _is_ip_literal(host) else _RESOLVED.get(host)
    if ip:                                   # 1. GeoIP по реальному IP
        res = _geoip_is_russia(ip)
        if res is not None:
            return res
    if host.endswith(RU_TLDS) or any(k in host for k in RU_DOMAIN_KEYWORDS):
        return True                          # 2. домен
    p = parse_link(url) if url else None
    if p:                                    # 3. тег и SNI
        if RU_TAG_RE.search(p['tag']):
            return True
        sni = (p['q'].get('sni') or '').lower()
        if sni and any(k in sni for k in RU_SNI_KEYWORDS):
            return True
    return False


# ============================================================
# ИМЕНА СЕРВЕРОВ: флаг + страна (+ «Белые списки»)
# ============================================================
COUNTRY_NAMES = {
    'AE': 'United Arab Emirates', 'AL': 'Albania', 'AM': 'Armenia', 'AR': 'Argentina',
    'AT': 'Austria', 'AU': 'Australia', 'AZ': 'Azerbaijan', 'BA': 'Bosnia and Herzegovina',
    'BD': 'Bangladesh', 'BE': 'Belgium', 'BG': 'Bulgaria', 'BH': 'Bahrain', 'BR': 'Brazil',
    'BY': 'Belarus', 'CA': 'Canada', 'CH': 'Switzerland', 'CL': 'Chile', 'CN': 'China',
    'CO': 'Colombia', 'CR': 'Costa Rica', 'CY': 'Cyprus', 'CZ': 'Czechia', 'DE': 'Germany',
    'DK': 'Denmark', 'EC': 'Ecuador', 'EE': 'Estonia', 'EG': 'Egypt', 'ES': 'Spain',
    'FI': 'Finland', 'FR': 'France', 'GB': 'United Kingdom', 'GE': 'Georgia', 'GR': 'Greece',
    'HK': 'Hong Kong', 'HR': 'Croatia', 'HU': 'Hungary', 'ID': 'Indonesia', 'IE': 'Ireland',
    'IL': 'Israel', 'IN': 'India', 'IR': 'Iran', 'IS': 'Iceland', 'IT': 'Italy',
    'JP': 'Japan', 'KG': 'Kyrgyzstan', 'KR': 'South Korea', 'KZ': 'Kazakhstan',
    'LT': 'Lithuania', 'LU': 'Luxembourg', 'LV': 'Latvia', 'MD': 'Moldova', 'ME': 'Montenegro',
    'MK': 'North Macedonia', 'MT': 'Malta', 'MX': 'Mexico', 'MY': 'Malaysia',
    'NL': 'Netherlands', 'NO': 'Norway', 'NZ': 'New Zealand', 'PA': 'Panama', 'PE': 'Peru',
    'PH': 'Philippines', 'PK': 'Pakistan', 'PL': 'Poland', 'PT': 'Portugal', 'RO': 'Romania',
    'RS': 'Serbia', 'RU': 'Russia', 'SA': 'Saudi Arabia', 'SE': 'Sweden', 'SG': 'Singapore',
    'SI': 'Slovenia', 'SK': 'Slovakia', 'TH': 'Thailand', 'TR': 'Turkey', 'TW': 'Taiwan',
    'UA': 'Ukraine', 'US': 'United States', 'UZ': 'Uzbekistan', 'VN': 'Vietnam',
    'ZA': 'South Africa',
}
_FLAG_RE   = re.compile('[\U0001F1E6-\U0001F1FF]{2}')
_WL_TAG_RE = re.compile(r'cidr|white|белы[ех]\s+списк|\bwl\b', re.I)
_WL_KEYS: set = set()      # ключи серверов, пришедших из «белых» источников
_NAMES: dict = {}          # url -> итоговое имя


def _is_whitelist_source(src_url: str) -> bool:
    if not src_url.startswith(_IGARECK):
        return False
    base = src_url.rsplit('/', 1)[-1].lower()
    return any(m in base for m in WHITELIST_SOURCE_MARKERS)


def _iso_to_flag(code: str) -> str:
    return ''.join(chr(0x1F1E6 + ord(c) - 65) for c in code.upper())


def _flag_to_iso(flag: str) -> str:
    return ''.join(chr(ord(c) - 0x1F1E6 + 65) for c in flag)


def _geoip_country(ip: str):
    if _geoip_reader is None:
        return None
    try:
        r = _geoip_reader.country(ip)
        return (r.country.iso_code, r.country.names.get('en')) if r.country.iso_code else None
    except Exception:
        return None


def _is_whitelist(url: str) -> bool:
    p = parse_link(url)
    if not p:
        return False
    return _dedup_key(p) in _WL_KEYS or bool(_WL_TAG_RE.search(p['tag']))


def _country_for(url: str, wl: bool) -> tuple:
    """(ISO-код, английское название). GeoIP по реальному IP; для «белых списков»
    приоритет у флага в исходном теге: там обычно страна выхода, а IP входа — российский."""
    p = parse_link(url)
    host = p['host'].lower()
    ip = host if _is_ip_literal(host) else _RESOLVED.get(host)
    geo = _geoip_country(ip) if ip else None
    geo_code = geo[0] if geo else None
    tag_codes = list(dict.fromkeys(_flag_to_iso(f) for f in _FLAG_RE.findall(p['tag'])))
    tag_code = tag_codes[0] if len(tag_codes) == 1 else None
    code = (tag_code or geo_code) if wl else (geo_code or tag_code)
    if not code:
        return '', 'Unknown'
    name = COUNTRY_NAMES.get(code) or (geo[1] if geo and geo[0] == code else None) or code
    return code, name


def _assign_names(results: list) -> int:
    """Формирует имена: «🔑 🇩🇪 Germany #1» / «🔑 🇵🇱 Белые списки | Poland #1»."""
    counters: dict = {}
    wl_count = 0
    for entry in results:
        url = entry[0]
        wl = _is_whitelist(url)
        code, cname = _country_for(url, wl)
        flag = _iso_to_flag(code) if code else '\U0001f310'
        name = f"{flag} {WHITELIST_LABEL} | {cname}" if wl else f"{flag} {cname}"
        if NAME_NUMBERING:
            n = counters[(wl, code)] = counters.get((wl, code), 0) + 1
            name += f" #{n}"
        if NAME_SHOW_SECURITY:
            name = f"{_get_security_level(url)[1]} {name}"
        _NAMES[url] = name
        wl_count += wl
    return wl_count


# ============================================================
# БЕЗОПАСНОСТЬ
# ============================================================

def _get_security(p: dict) -> str:
    if p['proto'] == 'ss':
        return 'shadowsocks'
    return (p['q'].get('security') or ('tls' if p['proto'] == 'trojan' else 'none')).lower()


def _get_network(p: dict) -> str:
    return (p['q'].get('type') or 'tcp').lower()


def _get_security_level(url: str) -> tuple:
    p = parse_link(url)
    bad = ('insecure', '\u26a0\ufe0f', 'Небезопасно: нет шифрования или allowInsecure=1')
    if not p:
        return bad
    if p['proto'] == 'ss':
        if p['method'] in AEAD_METHODS:
            return 'secure', '\U0001f512', 'Shadowsocks AEAD — шифрование на уровне протокола'
        return bad
    q   = p['q']
    sec = _get_security(p)
    if sec == 'reality':
        return 'reality', '\U0001f511', 'Reality/XTLS — максимальная защита'
    allow_insecure = (q.get('allowInsecure') or q.get('insecure') or '') in ('1', 'true')
    if sec == 'tls' and not allow_insecure:
        return 'secure', '\U0001f512', 'TLS — соединение защищено'
    if p['proto'] == 'vless' and (q.get('encryption') or 'none') != 'none':
        return 'secure', '\U0001f512', 'VLESS Encryption'
    return bad


def _check_pbk(url: str) -> bool:
    p = parse_link(url)
    if not p:
        return False
    if _get_security(p) != 'reality':
        return True
    pbk = (p['q'].get('pbk') or '').strip()
    if len(pbk) != 43 or not re.fullmatch(r'[A-Za-z0-9\-_]+', pbk):
        return False
    sid = p['q'].get('sid') or ''
    return len(sid) <= 16 and len(sid) % 2 == 0 and re.fullmatch(r'[0-9a-fA-F]*', sid) is not None


_sni_cache: dict = {}
_sni_lock = threading.Lock()


def _check_sni(url: str) -> bool:
    """Реальный TLS-хендшейк с проверкой сертификата на SNI-хост."""
    p = parse_link(url)
    sni = ((p['q'].get('sni') if p else '') or '').strip().lower()
    if not sni:
        return True
    with _sni_lock:
        if sni in _sni_cache:
            return _sni_cache[sni]
    try:
        ctx = ssl.create_default_context()
        with socket.create_connection((sni, 443), timeout=SNI_CHECK_TIMEOUT) as raw:
            with ctx.wrap_socket(raw, server_hostname=sni):
                pass
        result = True
    except Exception:
        result = False
    with _sni_lock:
        _sni_cache[sni] = result
    return result


# ============================================================
# ГЕНЕРАЦИЯ КОНФИГОВ XRAY (один билдер на все случаи)
# ============================================================

def _build_stream(p: dict) -> dict:
    q, host = p['q'], p['host']

    def g(k, d=''):
        return q.get(k) or d

    net = g('type', 'tcp').lower()
    net = {'h2': 'http', 'splithttp': 'xhttp', 'raw': 'tcp'}.get(net, net)
    sec = _get_security(p)
    sni = g('sni') or g('host') or host
    hdr_host = g('host') or sni
    path = g('path', '/')
    stream: dict = {"network": net, "security": sec}

    if net == 'ws':
        stream["wsSettings"] = {"path": path, "headers": {"Host": hdr_host}}
    elif net == 'httpupgrade':
        stream["httpupgradeSettings"] = {"path": path, "host": hdr_host}
    elif net == 'xhttp':
        xs = {"path": path, "mode": g('mode', 'auto')}
        if g('host'):
            xs["host"] = g('host')
        if g('extra'):
            try:
                xs["extra"] = json.loads(g('extra'))
            except ValueError:
                pass
        stream["xhttpSettings"] = xs
    elif net == 'grpc':
        stream["grpcSettings"] = {"serviceName": g('serviceName'),
                                  "multiMode": g('mode') == 'multi'}
    elif net == 'http':
        stream["httpSettings"] = {"host": [hdr_host], "path": path}
    elif net == 'kcp':
        ks = {"header": {"type": g('headerType', 'none')}}
        if g('seed'):
            ks["seed"] = g('seed')
        stream["kcpSettings"] = ks
    elif net == 'tcp' and g('headerType') == 'http':
        stream["tcpSettings"] = {"header": {"type": "http", "request": {
            "path": [path], "headers": {"Host": [hdr_host]}}}}

    if sec == 'reality':
        rs = {
            "serverName":  sni,
            "fingerprint": g('fp', 'chrome'),
            "publicKey":   g('pbk'),
            "shortId":     g('sid'),
            "spiderX":     g('spx', '/'),
        }
        if g('pqv'):
            rs["mldsa65Verify"] = g('pqv')
        stream["realitySettings"] = rs
    elif sec == 'tls':
        alpn = g('alpn')
        if alpn:
            alpn_list = alpn.split(',')
        elif net in ('ws', 'httpupgrade'):
            alpn_list = ['http/1.1']
        else:
            alpn_list = ['h2', 'http/1.1']
        stream["tlsSettings"] = {
            "serverName":    sni,
            "fingerprint":   g('fp', 'chrome'),
            "alpn":          alpn_list,
            "allowInsecure": (g('allowInsecure') or g('insecure')) in ('1', 'true'),
        }
    return stream


def build_outbound(p: dict, tag: str = 'proxy', dialer: str | None = None) -> dict:
    """Outbound для vless/trojan/ss. dialer — тег другого outbound (цепочка)."""
    if p['proto'] == 'vless':
        user = {"id": p['secret'], "encryption": p['q'].get('encryption') or 'none'}
        if p['q'].get('flow'):
            user["flow"] = p['q']['flow']
        out = {
            "tag": tag, "protocol": "vless",
            "settings": {"vnext": [{"address": p['host'], "port": p['port'], "users": [user]}]},
            "streamSettings": _build_stream(p),
        }
    elif p['proto'] == 'trojan':
        out = {
            "tag": tag, "protocol": "trojan",
            "settings": {"servers": [{"address": p['host'], "port": p['port'],
                                      "password": p['secret']}]},
            "streamSettings": _build_stream(p),
        }
    else:
        out = {
            "tag": tag, "protocol": "shadowsocks",
            "settings": {"servers": [{"address": p['host'], "port": p['port'],
                                      "method": p['method'], "password": p['password']}]},
        }
    if dialer:
        # ВАЖНО: цепочка в xray делается через sockopt.dialerProxy.
        # (Прежний "proxySettings" внутри streamSettings xray игнорирует —
        #  «цепочка» на самом деле шла напрямую.)
        out.setdefault("streamSettings", {}).setdefault("sockopt", {})["dialerProxy"] = dialer
    return out


def build_config(outbound: dict, port: int, extra_outbounds: tuple | list = ()) -> dict:
    return {
        "log": {"loglevel": "none"},
        "inbounds": [{"listen": "127.0.0.1", "port": port, "protocol": "http"}],
        "outbounds": [outbound, *extra_outbounds, {"tag": "block", "protocol": "blackhole"}],
    }


# ============================================================
# ЗАПУСК XRAY
# ============================================================

def _port_is_free(port: int) -> bool:
    with socket.socket() as s:
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            s.bind(('127.0.0.1', port))
            return True
        except OSError:
            return False


class PortPool:
    def __init__(self, start: int, count: int):
        self._q: queue.Queue = queue.Queue()
        for p in range(start, start + count):
            self._q.put(p)

    def acquire(self) -> int:
        while True:
            p = self._q.get(timeout=120)
            if _port_is_free(p):          # порт занят чужим процессом — выкидываем
                return p

    def release(self, p: int):
        self._q.put(p)


PORTS = PortPool(XRAY_PORT_BASE, XRAY_WORKERS * 3)


def _wait_for_port(port: int, timeout: float, proc: subprocess.Popen | None = None) -> bool:
    deadline = time.time() + timeout
    while time.time() < deadline:
        if proc is not None and proc.poll() is not None:
            return False                  # xray упал → порт «живой» только у чужака
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=0.2):
                return True
        except OSError:
            time.sleep(0.05)
    return False


@contextlib.contextmanager
def _xray(config: dict, port: int):
    fd, path = tempfile.mkstemp(suffix='.json', prefix='xray_')
    proc = None
    try:
        with os.fdopen(fd, 'w') as f:
            json.dump(config, f)
        proc = subprocess.Popen([XRAY_BIN, 'run', '-c', path],
                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        yield _wait_for_port(port, XRAY_START_TIMEOUT, proc)
    finally:
        if proc:
            try:
                proc.terminate()
                proc.wait(timeout=1.5)
            except Exception:
                with contextlib.suppress(Exception):
                    proc.kill()
        with contextlib.suppress(OSError):
            os.remove(path)


# ============================================================
# ЭТАП 1: TCP
# ============================================================

def _resolve_ipv4(host: str) -> str | None:
    try:
        ip = ipaddress.ip_address(host)
        return str(ip) if ip.version == 4 else None
    except ValueError:
        pass
    try:
        return socket.getaddrinfo(host, None, socket.AF_INET, socket.SOCK_STREAM)[0][4][0]
    except (OSError, UnicodeError):
        return None


def tcp_alive(url: str):
    p = parse_link(url)
    if not p or p['proto'] not in SUPPORTED_PROTOS or p['plugin']:
        return None
    host, port = p['host'], p['port']
    if len(host) > 253 or any(bad in host.lower() for bad in BLACK_LIST):
        return None
    ip = _resolve_ipv4(host)
    if ip is None:
        return None
    addr = ipaddress.ip_address(ip)
    if any(addr in net for net in BLOCKED_NETS):
        if _is_ip_literal(host) or BLOCK_CDN_BY_DNS:
            return None
    try:
        with socket.create_connection((ip, port), timeout=TCP_TIMEOUT):
            pass
    except OSError:
        return None
    _RESOLVED[host.lower()] = ip
    return url


# ============================================================
# ЭТАП 2: ПРОВЕРКА ЧЕРЕЗ XRAY
# ============================================================

def _status_ok(test_url: str, status: int) -> bool:
    if test_url.endswith('generate_204'):
        return status == 204
    return status in OK_STATUS


def _check_google_ban(session: requests.Session) -> bool:
    """False только при явном редиректе на captcha Google; всё прочее — пропускаем."""
    try:
        r = session.get("http://www.google.com/generate_204", timeout=4.0, allow_redirects=False)
        if r.status_code in (301, 302):
            loc = r.headers.get('Location', '').lower()
            if 'sorry.google' in loc or '/sorry/' in loc:
                return False
    except Exception:
        pass
    return True


def _tls_integrity(session: requests.Session) -> bool | None:
    """True — ок, False — подмена сертификата/контента, None — не удалось проверить."""
    try:
        r = session.get(INTEGRITY_URL, timeout=REQUEST_TIMEOUT, allow_redirects=False)
        if r.status_code == 204:
            return True
        return False if r.status_code == 200 else None
    except requests.exceptions.SSLError:
        return False
    except requests.RequestException:
        return None


def _measure(port: int):
    session = requests.Session()
    session.trust_env = False
    session.proxies = {"http": f"http://127.0.0.1:{port}", "https": f"http://127.0.0.1:{port}"}
    try:
        if CHECK_GOOGLE_BAN and not _check_google_ban(session):
            return None
        if FILTER_MITM or REQUIRE_HTTPS:
            ok = _tls_integrity(session)
            if (FILTER_MITM and ok is False) or (REQUIRE_HTTPS and ok is not True):
                return None

        pings, losses = [], 0
        for _ in range(PING_ROUNDS):
            ok = False
            for test_url in TEST_URLS:
                try:
                    t0 = time.perf_counter()
                    r = session.get(test_url, timeout=REQUEST_TIMEOUT, allow_redirects=False)
                    ms = int((time.perf_counter() - t0) * 1000)
                    if _status_ok(test_url, r.status_code):
                        pings.append(ms)
                        ok = True
                        break
                except requests.RequestException:
                    continue
            if not ok:
                losses += 1

        if not pings or losses / PING_ROUNDS > MAX_LOSS_RATE:
            return None
        avg = int(statistics.median(pings))
        if avg > MAX_PING_MS:
            return None
        jitter = int(statistics.stdev(pings)) if len(pings) > 1 else 0
        return avg + jitter // 2, avg, jitter, losses
    finally:
        session.close()


def test_via_xray(url: str, ru_url: str | None = None):
    """Возвращает (url, score, avg, jitter, losses) или None.
    Если задан ru_url — зарубежный сервер проверяется через него (цепочка)."""
    p = parse_link(url)
    if not p or p['proto'] not in SUPPORTED_PROTOS:
        return None
    extra = []
    if ru_url:
        rp = parse_link(ru_url)
        if not rp:
            return None
        extra = [build_outbound(rp, tag='ru')]
    out = build_outbound(p, tag='proxy', dialer='ru' if ru_url else None)

    port = PORTS.acquire()
    try:
        with _xray(build_config(out, port, extra), port) as started:
            if not started:
                return None
            m = _measure(port)
            return (url, *m) if m else None
    except Exception:
        return None
    finally:
        PORTS.release(port)


_chain_ru_urls: list = []


def _test_via_chain(url: str):
    best = None
    for ru in random.sample(_chain_ru_urls, min(CHAIN_TRIES, len(_chain_ru_urls))):
        res = test_via_xray(url, ru_url=ru)
        if res and (best is None or res[2] < best[2]):
            best = res
    return best


# ============================================================
# СБОР КОНФИГОВ
# ============================================================

def _decode_subscription(text: str) -> str:
    stripped = text.strip()
    if PROTO_REGEX.search(stripped):
        return stripped
    for variant in (stripped, stripped.replace('-', '+').replace('_', '/')):
        decoded = _b64decode(re.sub(r'\s+', '', variant))
        if decoded and PROTO_REGEX.search(decoded):
            return decoded
    lines = []
    for line in stripped.splitlines():
        line = line.strip()
        if not line:
            continue
        if PROTO_REGEX.search(line):
            lines.append(line)
            continue
        dec = _b64decode(line)
        if dec and PROTO_REGEX.search(dec):
            lines.append(dec)
    return '\n'.join(lines) if lines else stripped


def _fetch_with_retry(url: str, retries: int = 3, delay: float = 2.0):
    headers = {'User-Agent': 'Mozilla/5.0'}
    candidates = [url] + [m + url[len(p):] for p, m in MIRRORS.items() if url.startswith(p)]
    for cand in candidates:
        for attempt in range(1, retries + 1):
            try:
                r = requests.get(cand, timeout=15, headers=headers)
                r.raise_for_status()
                if cand != url:
                    print(f"  [MIRROR] {url.rsplit('/', 1)[-1]} загружен с зеркала")
                return r.text
            except Exception as e:
                if attempt < retries:
                    print(f"  [RETRY {attempt}/{retries}] {cand}: {e}")
                    time.sleep(delay)
                else:
                    print(f"  [WARN] Не удалось загрузить: {cand}: {e}")
    return None


def _dedup_key(p: dict) -> tuple:
    """Ключ «один и тот же сервер». Варианты fp (chrome/edge/ios/qq...) и мусорные
    параметры (host=?TELEGRAM..., headerType=) — это ОДИН сервер, не разные."""
    if p['proto'] == 'ss':
        return ('ss', p['host'].lower(), p['port'], p['method'], p['password'])
    q = p['q']
    net = (q.get('type') or 'tcp').lower()
    net = {'raw': 'tcp', 'h2': 'http', 'splithttp': 'xhttp'}.get(net, net)
    keys = ['security', 'sni', 'pbk', 'sid', 'flow', 'encryption', 'alpn',
            'allowInsecure', 'insecure']
    if net != 'tcp':
        keys += ['path', 'host', 'serviceName', 'mode', 'extra', 'authority', 'seed', 'headerType']
    return (p['proto'], p['host'].lower(), p['port'], p['secret'], net,
            tuple((k, q.get(k, '')) for k in keys))


def fetch_configs() -> list:
    with cf.ThreadPoolExecutor(max_workers=len(SOURCES)) as ex:
        texts = list(ex.map(_fetch_with_retry, SOURCES))

    all_raw = []
    for src, raw in zip(SOURCES, texts):
        if raw is None:
            continue
        text = _decode_subscription(raw)
        found = PROTO_REGEX.findall(text)
        fmt = "plain" if text == raw.strip() else "base64"
        print(f"  [OK] {src.rsplit('/', 1)[-1]}  ->  {len(found)}  [{fmt}]")
        wl = _is_whitelist_source(src)
        all_raw.extend((c, wl) for c in found)

    seen_keys, per_endpoint, unique = set(), {}, []
    for cfg, wl in all_raw:
        p = parse_link(cfg)
        if not p:
            continue
        key = _dedup_key(p)
        if wl:
            _WL_KEYS.add(key)
        if key in seen_keys:
            continue
        seen_keys.add(key)
        ep = f"{p['host'].lower()}:{p['port']}"
        if per_endpoint.get(ep, 0) >= MAX_PER_ENDPOINT:
            continue
        per_endpoint[ep] = per_endpoint.get(ep, 0) + 1
        unique.append(cfg)
    return unique


def _static_filter(urls: list) -> tuple[list, dict]:
    """Дешёвые фильтры ДО сетевых проверок — экономят десятки минут xray-времени."""
    counts = {'insecure': 0, 'lock': 0, 'pbk': 0, 'bad': 0}
    keep = []
    for u in urls:
        p = parse_link(u)
        if not p or p['proto'] not in SUPPORTED_PROTOS or p['plugin']:
            counts['bad'] += 1
            continue
        level = _get_security_level(u)[0]
        if FILTER_INSECURE and level == 'insecure':
            counts['insecure'] += 1
        elif FILTER_LOCK and level == 'secure':
            counts['lock'] += 1
        elif FILTER_INVALID_PBK and not _check_pbk(u):
            counts['pbk'] += 1
        else:
            keep.append(u)
    return keep, counts


# ============================================================
# HTML
# ============================================================

def _esc(s) -> str:
    return html_lib.escape(str(s), quote=True)


HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="ru">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>VPN Scout</title>
<style>
body { margin:0; padding:0; background:#0a0c10; color:#e2e8f0; font-family:Arial,sans-serif; font-size:13px; }
h1 { margin:0; padding:20px 20px 0; font-size:24px; color:#fff; }
.info { padding:8px 20px 16px; color:#718096; font-size:12px; }
.info b { color:#00e5ff; }
.legend { padding:0 20px 10px; font-size:11px; color:#718096; display:flex; gap:16px; flex-wrap:wrap; }
.stats-row { display:flex; gap:10px; padding:0 20px 10px; flex-wrap:wrap; }
.stat { flex:1; min-width:120px; background:#111318; border:1px solid #1e2230; border-radius:8px; padding:14px 18px; text-align:center; }
.stat-num { font-size:26px; font-weight:700; color:#fff; }
.stat-lbl { font-size:11px; color:#718096; margin-top:4px; }
.tab-bar { padding:10px 20px; display:flex; align-items:center; flex-wrap:wrap; gap:8px; }
.tab-btn { padding:10px 30px; border-radius:8px; border:2px solid #1e2230; background:#111318; color:#e2e8f0; font-size:14px; font-weight:700; cursor:pointer; }
.tab-btn.active-intl { background:#00e5ff; color:#000; border-color:#00e5ff; }
.tab-btn.active-ru  { background:#ff6b35; color:#fff; border-color:#ff6b35; }
.section { display:none; padding:0 20px 40px; }
.section.visible { display:block; }
.tbl-wrap { overflow-x:auto; border:1px solid #1e2230; border-radius:8px; }
table { width:100%; border-collapse:collapse; background:#111318; }
thead th { background:#0d1017; color:#718096; font-size:10px; text-transform:uppercase; padding:11px 12px; text-align:left; border-bottom:1px solid #1e2230; white-space:nowrap; }
tbody tr:hover { background:#161b26; }
#toast { position:fixed; bottom:24px; right:24px; background:#06d6a0; color:#000; font-weight:700; padding:10px 20px; border-radius:8px; opacity:0; transition:opacity .3s; pointer-events:none; z-index:999; }
#toast.show { opacity:1; }
</style>
</head>
<body>
<h1>VPN Scout</h1>
<div class="info">Обновлено: <b>__UPDATED__</b> &nbsp;|&nbsp; Время проверки: <b>__ELAPSED__с</b> &nbsp;|&nbsp; Пинг измерен с сервера проверки, не с вашего IP</div>
<div class="legend">
  <span>🔑 Reality/XTLS</span><span>🔒 TLS / SS-AEAD</span><span>⚠️ Небезопасно</span>
</div>
<div class="stats-row">
  <div class="stat"><div class="stat-num" style="color:#00e5ff">__N_INTL__</div><div class="stat-lbl">🌍 Зарубежных</div></div>
  <div class="stat"><div class="stat-num" style="color:#ff6b35">__N_RU__</div><div class="stat-lbl">🇷🇺 Российских</div></div>
  <div class="stat"><div class="stat-num">__TOTAL__</div><div class="stat-lbl">Всего живых</div></div>
  <div class="stat"><div class="stat-num" style="color:#06d6a0">__BEST__ms</div><div class="stat-lbl">Лучший пинг</div></div>
</div>
<div class="tab-bar">
  <button class="tab-btn active-intl" id="btn-intl" onclick="showTab('intl')">🌍 Зарубежные (__N_INTL__)</button>
  <button class="tab-btn" id="btn-ru" onclick="showTab('ru')">🇷🇺 Российские (__N_RU__)</button>
  <button id="btn-pingall" onclick="pingAll()" style="margin-left:auto;background:#1a1040;border:2px solid #a78bfa;color:#a78bfa;border-radius:8px;padding:10px 22px;font-size:14px;font-weight:700;cursor:pointer">
    ⚡ Грубая проверка хоста с моего IP
  </button>
  <span id="ping-status" style="font-size:12px;color:#718096"></span>
</div>
<div class="section visible" id="sec-intl"><div class="tbl-wrap"><table>
  <thead><tr><th>#</th><th>Сервер</th><th>Протокол</th><th>Транспорт</th><th>Безопасность</th><th>🔒</th><th>Пинг</th><th>Jitter</th><th>Loss</th><th></th></tr></thead>
  <tbody>__ROWS_INTL__</tbody>
</table></div></div>
<div class="section" id="sec-ru"><div class="tbl-wrap"><table>
  <thead><tr><th>#</th><th>Сервер</th><th>Протокол</th><th>Транспорт</th><th>Безопасность</th><th>🔒</th><th>Пинг</th><th>Jitter</th><th>Loss</th><th></th></tr></thead>
  <tbody>__ROWS_RU__</tbody>
</table></div></div>
<div id="toast">Скопировано!</div>
<script>
function showTab(name) {
  document.getElementById('sec-intl').className = 'section' + (name === 'intl' ? ' visible' : '');
  document.getElementById('sec-ru').className   = 'section' + (name === 'ru'   ? ' visible' : '');
  document.getElementById('btn-intl').className = 'tab-btn' + (name === 'intl' ? ' active-intl' : '');
  document.getElementById('btn-ru').className   = 'tab-btn' + (name === 'ru'   ? ' active-ru'   : '');
}
async function copyText(text) {
  if (navigator.clipboard && window.isSecureContext) { await navigator.clipboard.writeText(text); return; }
  var ta = document.createElement('textarea');
  ta.value = text; ta.style.position = 'fixed'; ta.style.left = '-9999px';
  document.body.appendChild(ta); ta.select(); document.execCommand('copy'); document.body.removeChild(ta);
}
async function copyVpn(btn) {
  try {
    await copyText(btn.getAttribute('data-url'));
    btn.textContent = 'OK!';
    var t = document.getElementById('toast'); t.className = 'show';
    setTimeout(function() { btn.textContent = 'Copy'; t.className = ''; }, 1500);
  } catch (e) { alert('Не удалось скопировать'); }
}
// Браузер не умеет raw TCP, поэтому это ГРУБАЯ оценка: достижим ли хост по HTTPS.
// Reality/не-HTTP серверы могут показывать ✗ даже будучи рабочими.
async function pingHost(host) {
  if (!host) return null;
  var targets = ['https://' + host + '/favicon.ico', 'https://' + host + '/'];
  for (var i = 0; i < targets.length; i++) {
    try {
      var t0 = performance.now();
      await fetch(targets[i], { mode: 'no-cors', cache: 'no-store', signal: AbortSignal.timeout(5000) });
      return Math.round(performance.now() - t0);
    } catch (e) {}
  }
  return null;
}
async function pingAll() {
  var btn = document.getElementById('btn-pingall');
  var status = document.getElementById('ping-status');
  btn.disabled = true; btn.style.opacity = '0.6';
  var spans = Array.from(document.querySelectorAll('.ping-live'));
  var done = 0, BATCH = 10;
  for (var i = 0; i < spans.length; i += BATCH) {
    await Promise.all(spans.slice(i, i + BATCH).map(async function(span) {
      span.textContent = '...';
      var ms = await pingHost(span.getAttribute('data-host'));
      done++; status.textContent = done + '/' + spans.length;
      if (ms === null) { span.textContent = '✗'; span.style.color = '#ef476f'; }
      else { span.textContent = ms + 'ms'; span.style.color = ms < 300 ? '#06d6a0' : ms < 1000 ? '#ffd166' : '#ef476f'; }
    }));
  }
  btn.disabled = false; btn.style.opacity = '1';
  status.textContent = '✓ Готово (' + spans.length + ')';
}
</script>
</body>
</html>"""


def generate_html_viewer(intl_results: list, ru_results: list, elapsed: int) -> str:
    def ping_color(avg):
        return '#06d6a0' if avg < 300 else '#ffd166' if avg < 1000 else '#ef476f'

    badge = ('background:#1a1f2e;color:#9aa0b4;border:1px solid #2a3040;'
             'border-radius:4px;padding:2px 7px;font-size:11px')
    sec_colors = {'reality': '#a78bfa', 'secure': '#06d6a0', 'insecure': '#ef476f'}

    def make_rows(results):
        if not results:
            return ('<tr><td colspan="10" style="text-align:center;padding:30px;'
                    'color:#718096">Нет серверов</td></tr>')
        rows = []
        for i, (url, _score, avg, jitter, losses) in enumerate(results, 1):
            p = parse_link(url) or {'proto': '?', 'host': '', 'tag': '', 'q': {}}
            host = p['host']
            tag = _NAMES.get(url) or (p['tag'] or host)[:40]
            loss_pct = int(losses / PING_ROUNDS * 100)
            level, icon, tip = _get_security_level(url)
            sec = _get_security(p) if p['proto'] != '?' else '?'
            net = _get_network(p) if p['proto'] != '?' else '?'
            rows.append(
                '<tr style="border-bottom:1px solid #1e2230">'
                f'<td style="padding:9px 10px;color:#4a5568">{i}</td>'
                f'<td style="padding:9px 10px;max-width:200px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">{_esc(tag)}</td>'
                f'<td style="padding:9px 10px"><span style="background:#0d2b33;color:#00e5ff;border:1px solid #005f6b;border-radius:4px;padding:2px 7px;font-size:11px;font-weight:700">{_esc(p["proto"].upper())}</span></td>'
                f'<td style="padding:9px 10px"><span style="{badge}">{_esc(net)}</span></td>'
                f'<td style="padding:9px 10px"><span style="{badge}">{_esc(sec)}</span></td>'
                f'<td style="padding:9px 10px;text-align:center"><span title="{_esc(tip)}" style="font-size:15px;cursor:help;color:{sec_colors[level]}">{icon}</span></td>'
                f'<td style="padding:9px 10px;color:{ping_color(avg)};font-weight:700">{avg}ms</td>'
                f'<td style="padding:9px 10px;color:#718096">{jitter}ms</td>'
                f'<td style="padding:9px 10px;color:{"#06d6a0" if loss_pct == 0 else "#ef476f"}">{loss_pct}%</td>'
                f'<td style="padding:9px 10px;white-space:nowrap"><button onclick="copyVpn(this)" data-url="{_esc(url)}" style="background:#0d2b33;border:1px solid #005f6b;color:#00e5ff;border-radius:5px;padding:4px 10px;cursor:pointer;font-size:13px;margin-right:6px">Copy</button>'
                f'<span class="ping-live" data-host="{_esc(host)}" style="font-size:12px;color:#4a5568">—</span></td>'
                '</tr>'
            )
        return '\n'.join(rows)

    repl = {
        '__UPDATED__':  time.strftime('%d.%m.%Y %H:%M UTC', time.gmtime()),
        '__ELAPSED__':  str(elapsed),
        '__N_INTL__':   str(len(intl_results)),
        '__N_RU__':     str(len(ru_results)),
        '__TOTAL__':    str(len(intl_results) + len(ru_results)),
        '__BEST__':     str(min((r[2] for r in intl_results), default=0)),
        '__ROWS_INTL__': make_rows(intl_results),
        '__ROWS_RU__':   make_rows(ru_results),
    }
    out = HTML_TEMPLATE
    for k, v in repl.items():
        out = out.replace(k, v)
    return out


# ============================================================
# ВЫВОД
# ============================================================

def _tagged_url(url: str) -> str:
    """Подписывает конфиг красивым именем; фрагмент корректно percent-кодируется."""
    p = parse_link(url)
    name = _NAMES.get(url)
    if not name:
        name = f"{p['host']}:{p['port']}" if p else 'server'
    return f"{url.split('#', 1)[0]}#{urllib.parse.quote(name)}"


def _print_breakdown(results: list):
    from collections import Counter
    c = Counter()
    for r in results:
        p = parse_link(r[0])
        if p:
            c[(p['proto'], _get_security(p), _get_network(p))] += 1
    print("  Структура финала (протокол / security / транспорт):")
    for (a, b, n), k in c.most_common():
        print(f"    {a}/{b}/{n}: {k}")


def _update_gist(files: dict):
    token = os.environ.get('GH_TOKEN')
    if not token:
        with contextlib.suppress(Exception):
            token = subprocess.run(["gh", "auth", "token"], capture_output=True,
                                   text=True).stdout.strip()
    if not token:
        print(" Не удалось получить токен GitHub (GH_TOKEN)!")
        return
    payload = json.dumps({"files": {n: {"content": c} for n, c in files.items()}}).encode()
    req = url_req.Request(
        f"https://api.github.com/gists/{GID}", data=payload, method="PATCH",
        headers={
            "Authorization": f"Bearer {token}", "Content-Type": "application/json",
            "Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28",
        })
    try:
        with url_req.urlopen(req, timeout=30) as resp:
            print(" Gist обновлён." if resp.status == 200 else f" Gist: статус {resp.status}")
    except urllib.error.HTTPError as e:
        print(f" Gist ошибка: {e.code} {e.read()[:200]!r}")
    except Exception as e:
        print(f" Gist ошибка: {e}")


# ============================================================
# ГЛАВНЫЙ ЗАПУСК
# ============================================================

def run():
    t_start = time.time()

    if shutil.which(XRAY_BIN) is None:
        raise SystemExit(f"Не найден бинарник xray ('{XRAY_BIN}'). Установите его или задайте XRAY_BIN.")
    ver = subprocess.run([XRAY_BIN, 'version'], capture_output=True, text=True).stdout.splitlines()

    print("=" * 60)
    print("  VPN SCOUT 2.0")
    print(f"  {ver[0] if ver else 'xray: версия неизвестна'}")
    print(f"  TCP: {TCP_WORKERS} воркеров / {TCP_TIMEOUT}с;  xray: {XRAY_WORKERS} воркеров")
    print(f"  Раундов: {PING_ROUNDS}, макс. пинг: {MAX_PING_MS}мс, MITM-проверка: {'ВКЛ' if FILTER_MITM else 'ВЫКЛ'}")
    print(f"  Цепочка через РФ: {'ВКЛ' if CHAIN_PROXY else 'ВЫКЛ'}")
    print("=" * 60)

    _init_geoip()

    print("\n[1/5] Сбор конфигов...")
    configs = fetch_configs()
    print(f"      Уникальных серверов (без дублей по fp; до {MAX_PER_ENDPOINT} вариантов на host:port): {len(configs)}")
    if not configs:
        print("Нет кандидатов.")
        return

    configs, cnt = _static_filter(configs)
    print(f"[2/5] Статические фильтры: осталось {len(configs)} "
          f"(небезоп.: {cnt['insecure']}, TLS-only: {cnt['lock']}, pbk/sid: {cnt['pbk']}, "
          f"неподдерж.: {cnt['bad']})")

    print(f"\n[3/5] TCP-проверка ({TCP_WORKERS} воркеров)...")
    with cf.ThreadPoolExecutor(max_workers=TCP_WORKERS) as ex:
        alive = [r for r in ex.map(tcp_alive, configs) if r]
    print(f"      TCP живых: {len(alive)} / {len(configs)}  ({int(time.time() - t_start)}с)")
    if not alive:
        print("Нет живых серверов после TCP-проверки.")
        return

    if FILTER_RUSSIAN and not CHAIN_PROXY:      # экономим xray-время
        before = len(alive)
        alive = [u for u in alive if not _is_russian_server(parse_link(u)['host'], u)]
        print(f"      Российских отброшено до xray: {before - len(alive)}")

    print(f"\n[4/5] xray-проверка {len(alive)} серверов ({XRAY_WORKERS} воркеров)...")
    results, total = [], len(alive)
    with cf.ThreadPoolExecutor(max_workers=XRAY_WORKERS) as ex:
        for n, res in enumerate(ex.map(test_via_xray, alive), 1):
            if res:
                results.append(res)
            if n % 25 == 0 or n == total:
                print(f"  Прогресс: {n}/{total}  |  прошли: {len(results)}")

    print("\n[5/5] Постобработка и сохранение...")
    if not results:
        print("Нет рабочих серверов.")
        return
    results.sort(key=lambda x: x[1])

    ru_pool, intl_pool = [], []
    for e in results:
        (ru_pool if _is_russian_server(parse_link(e[0])['host'], e[0]) else intl_pool).append(e)

    if CHAIN_PROXY and ru_pool and intl_pool:
        _chain_ru_urls[:] = [e[0] for e in ru_pool[:CHAIN_TOP_N]
                             if parse_link(e[0])['proto'] in ('vless', 'trojan', 'ss')]
        print(f"  Цепочка: перепроверяем {len(intl_pool)} зарубежных через {len(_chain_ru_urls)} РФ-входов...")
        chained = []
        with cf.ThreadPoolExecutor(max_workers=XRAY_WORKERS) as ex:
            for n, res in enumerate(ex.map(_test_via_chain, [e[0] for e in intl_pool]), 1):
                if res:
                    chained.append(res)
                if n % 25 == 0 or n == len(intl_pool):
                    print(f"  Цепочка: {n}/{len(intl_pool)}  |  прошли: {len(chained)}")
        intl_pool = chained
    elif CHAIN_PROXY:
        print("  Цепочка пропущена: нет российских или зарубежных серверов.")

    if FILTER_RUSSIAN:
        ru_pool = []

    if FILTER_DEAD_SNI:
        uniq = list({e[0] for e in intl_pool + ru_pool})
        print(f"  Проверка SNI ({len(uniq)} уник.)...")
        with cf.ThreadPoolExecutor(max_workers=30) as ex:
            list(ex.map(_check_sni, uniq))
        intl_pool = [e for e in intl_pool if _check_sni(e[0])]
        ru_pool   = [e for e in ru_pool   if _check_sni(e[0])]

    intl_results = sorted(intl_pool, key=lambda x: x[1])[:TOP_N_EACH]
    ru_results   = sorted(ru_pool,   key=lambda x: x[1])[:TOP_N_EACH]
    wl_i = _assign_names(intl_results)
    wl_r = _assign_names(ru_results)
    print(f"  Помечено «{WHITELIST_LABEL}»: {wl_i} из {len(intl_results)} зарубежных, "
          f"{wl_r} из {len(ru_results)} российских")
    elapsed = int(time.time() - t_start)

    print(f"\n{'─' * 60}")
    print(f"  Зарубежных: {len(intl_results)}   Российских: {len(ru_results)}   Время: {elapsed}с")
    print(f"{'─' * 60}")
    for i, (url, _s, avg, jitter, losses) in enumerate(intl_results[:10], 1):
        p = parse_link(url)
        print(f"  {i:<3}{avg:>5}мс  jitter:{jitter:>4}  loss:{losses}/{PING_ROUNDS}  "
              f"{_NAMES.get(url, p['host'])}")

    _print_breakdown(intl_results + ru_results)

    if not intl_results:
        print("Зарубежных серверов после фильтров нет — файлы не перезаписываются.")
        return

    vps_text = "\n".join(_tagged_url(r[0]) for r in intl_results)
    sub_text = base64.b64encode(vps_text.encode("utf-8")).decode("ascii")
    html_text = generate_html_viewer(intl_results, ru_results, elapsed)

    files = {FILE_NAME: vps_text, SUB_FILE: sub_text, VIEWER_FILE: html_text}
    if PUBLISH_RU_FILES and ru_results:
        ru_text = "\n".join(_tagged_url(r[0]) for r in ru_results)
        files[RU_FILE] = ru_text
        files[RU_SUB_FILE] = base64.b64encode(ru_text.encode("utf-8")).decode("ascii")
    for name, content in files.items():
        with open(name, "w", encoding="utf-8") as f:
            f.write(content)
    print(f"\n Сохранено: {FILE_NAME} ({len(intl_results)}), {SUB_FILE}, {VIEWER_FILE}")

    if GID:
        print("Обновляем Gist...")
        _update_gist(files)
    else:
        print("  MY_GIST_ID не задан.")


if __name__ == "__main__":
    run()