#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
VPN Scout 3.0

Собирает публичные VLESS / Trojan / Shadowsocks конфиги, проверяет их через
xray и публикует результат (vps.txt, sub.txt, index.html) в GitHub Gist.

Зависимости: requests, geoip2 (опционально), бинарник xray в PATH.
"""
from __future__ import annotations

import base64
import collections
import concurrent.futures as cf
import contextlib
import functools
import hashlib
import bisect
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
OBSOLETE_GIST_FILES = ("index.html",)   # старый HTML-просмотрщик: удаляется из Gist
XRAY_BIN    = os.environ.get('XRAY_BIN', 'xray')
TOP_N_EACH  = 900
GEOIP_DB_PATH = os.environ.get('GEOIP_DB', 'GeoLite2-Country.mmdb')

# --- Фильтры ---
FILTER_INSECURE    = on    # скрыть ⚠️ небезопасные (нет шифрования / allowInsecure=1)
FILTER_LOCK        = on   # скрыть 🔒 обычный TLS (оставить только Reality 🔑)
FILTER_RUSSIAN     = off   # скрыть 🇷🇺 российские серверы
FILTER_INVALID_PBK = on    # скрыть Reality с битым pbk/sid
FILTER_MITM        = on    # скрыть серверы, подменяющие HTTPS-сертификаты
NAME_SHOW_SECURITY = on    # NEW: иконка защиты в начале имени (🔑 Reality / 🔒 TLS / ⚠️)
NAME_NUMBERING     = on    # NEW: «Germany #1, #2…» (нумерация по пингу внутри группы)
WHITELIST_LABEL    = "Белые списки"

# ---------------------------------------------------------------------------
# БЕЛЫЕ СПИСКИ: определяет сам код, а не подписи в источниках
# ---------------------------------------------------------------------------
WL_DETECT = on
# 'both' — IP сервера в белом списке подсетей И SNI в белом списке доменов
#          (операторы переходят именно на такую связку: одного правильного SNI мало,
#           если IP сервера не в списке); 'ip' | 'sni' | 'any' — мягче.
WL_RULE = 'both'
WL_IP_LISTS = [      # подсети, доступные в мобильных сетях РФ при белых списках
    "https://raw.githubusercontent.com/ancored/ru-mobile-whitelist/release/ru-mobile-whitelist-ip.txt",
    "https://cdn.jsdelivr.net/gh/hxehex/russia-mobile-internet-whitelist/cidrwhitelist.txt",
    "https://raw.githubusercontent.com/escapingworm/russia-whitelist/refs/heads/main/ru-whitelist-cidr.txt",
    "https://cdn.jsdelivr.net/gh/hydraponique/roscomvpn-geoip/release/text/whitelist.txt",
]
WL_SNI_LISTS = [     # домены (SNI), которые пропускает фильтр
    "https://raw.githubusercontent.com/ancored/ru-mobile-whitelist/release/ru-mobile-whitelist-sni.txt",
    "https://cdn.jsdelivr.net/gh/hxehex/russia-mobile-internet-whitelist/whitelist.txt",
]
# Ваши собственные подтверждённые серверы: вставьте в этот файл Gist список ссылок,
# которые реально работали у вас при включённых белых списках (экспорт из клиента).
WL_GOOD_FILE = "whitelist_good.txt"
# Если ЭТОТ скрипт запущен внутри сети с белыми списками (например, на телефоне в Termux),
# он сам это обнаружит: напрямую доступны российские сайты, а зарубежные — нет.
RU_CONTROL_URLS = ["https://ya.ru/", "https://vk.com/"]
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

# ---------------------------------------------------------------------------
# НАДЁЖНОСТЬ ПРОВЕРКИ (v3)
# ---------------------------------------------------------------------------
# Пинг и потери меряются ТОЛЬКО по HTTPS с проверкой сертификата (как реальный тест
# в v2rayNG/Happ). Голый HTTP больше не засчитывается.
HTTPS_TARGETS = [
    "https://www.gstatic.com/generate_204",
    "https://cp.cloudflare.com/generate_204",
]
HIJACK_CHECK    = on       # прокси, «отвечающий» на несуществующий домен, — заглушка/перехват DNS
DATA_TEST       = on       # реальная передача данных, а не только ответ 204
DATA_TEST_BYTES = 300_000
DATA_TEST_URL   = f"https://speed.cloudflare.com/__down?bytes={DATA_TEST_BYTES}"
DATA_TEST_MAX_SEC = 15.0
MIN_KBPS        = 40       # минимальная скорость в тесте передачи данных, КБ/с

PROBE_HANDSHAKE      = on  # прямое TLS/Reality-рукопожатие с сервером ДО xray
PROBE_TIMEOUT        = 4.0
PROBE_RETRIES        = 2
PROBE_STRICT_TLS     = on  # TLS/Trojan: битый/просроченный сертификат = отсев
PROBE_STRICT_REALITY = off # Reality: пока только статистика (см. лог), включите после калибровки

CONFIRM_PASS    = on       # повторная проверка выживших через CONFIRM_DELAY секунд
CONFIRM_DELAY   = 15

HISTORY_FILE         = "history.json"   # хранится в Gist рядом с подпиской
HISTORY_RUNS         = 12               # сколько последних запусков помнить
HISTORY_MAX_AGE_DAYS = 14
MIN_HISTORY_RUNS     = 3                # с какого числа запусков включается фильтр по аптайму
MIN_UPTIME           = 0.5              # ниже — сервер «мигает» и не публикуется

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
_NAMES: dict = {}          # url -> итоговое имя


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


# ---------- определение «белых списков» ----------
_WL_IPS = None                 # IPSet подсетей
_WL_SNIS: set = set()          # суффиксы доменов
_GOOD_IDS: set = set()         # серверы, подтверждённые вами
_GOOD_PREFIXES: set = set()    # /24 подтверждённых серверов
_GOOD_SNIS: set = set()
_RESTRICTED_NET = False        # скрипт запущен ВНУТРИ сети с белыми списками
_DOMAIN_OK = re.compile(r'^[a-z0-9][a-z0-9._-]*$')


class IPSet:
    """Быстрая проверка вхождения IPv4 в набор подсетей (слияние + bisect)."""
    def __init__(self, nets):
        merged = ipaddress.collapse_addresses(nets)
        self._starts, self._ends = [], []
        for n in sorted(merged, key=lambda n: int(n.network_address)):
            self._starts.append(int(n.network_address))
            self._ends.append(int(n.broadcast_address))

    def __len__(self):
        return len(self._starts)

    def __contains__(self, ip: str) -> bool:
        try:
            n = int(ipaddress.IPv4Address(ip))
        except ValueError:
            return False
        i = bisect.bisect_right(self._starts, n) - 1
        return i >= 0 and n <= self._ends[i]


def _parse_cidr_text(text: str) -> list:
    nets = []
    for line in text.splitlines():
        tok = line.split('#', 1)[0].strip().split()
        if not tok:
            continue
        try:
            net = ipaddress.ip_network(tok[0], strict=False)
        except ValueError:
            continue
        if net.version == 4 and net.prefixlen >= 8:
            nets.append(net)
    return nets


def _parse_sni_text(text: str) -> set:
    out = set()
    for line in text.splitlines():
        tok = line.split('#', 1)[0].strip().lower()
        if not tok or ' ' in tok or '/' in tok:
            continue
        if tok.startswith(('keyword:', 'regexp:', 'geosite:', 'ext:')):
            continue
        for pref in ('domain:', 'full:', '*.', '.'):
            if tok.startswith(pref):
                tok = tok[len(pref):]
        tok = tok.rstrip('.')
        if not tok or '.' not in tok:
            continue
        if not tok.isascii():
            try:
                tok = tok.encode('idna').decode('ascii')
            except UnicodeError:
                continue
        if _DOMAIN_OK.match(tok):
            out.add(tok)
    return out


def _sni_whitelisted(sni: str, pool: set | None = None) -> bool:
    pool = _WL_SNIS if pool is None else pool
    parts = sni.lower().rstrip('.').split('.')
    return any('.'.join(parts[i:]) in pool for i in range(len(parts) - 1))


def _prefix24(ip: str) -> str:
    return str(ipaddress.ip_network(f"{ip}/24", strict=False))


def _server_id(p: dict) -> tuple:
    return (p['proto'], p['host'].lower(), p['port'], p.get('secret') or p.get('password'))


def load_whitelist_db() -> bool:
    """Загружает белые списки (подсети + домены). Пустой результат = детектор слеп."""
    global _WL_IPS
    urls = WL_IP_LISTS + WL_SNI_LISTS
    with cf.ThreadPoolExecutor(max_workers=len(urls)) as ex:
        texts = dict(zip(urls, ex.map(lambda u: _fetch_with_retry(u, retries=2, delay=1.0), urls)))
    nets, snis = [], set()
    for u in WL_IP_LISTS:
        got = _parse_cidr_text(texts[u]) if texts[u] else []
        print(f"  [WL-IP ] {u.rsplit('/', 1)[-1]}: {len(got)}")
        nets += got
    for u in WL_SNI_LISTS:
        got = _parse_sni_text(texts[u]) if texts[u] else set()
        print(f"  [WL-SNI] {u.rsplit('/', 1)[-1]}: {len(got)}")
        snis |= got
    _WL_IPS = IPSet(nets) if nets else None
    _WL_SNIS.clear()
    _WL_SNIS.update(snis)
    print(f"      Белые списки: {len(_WL_IPS) if _WL_IPS else 0} подсетей (после слияния), {len(_WL_SNIS)} доменов")
    if _WL_IPS is None or not _WL_SNIS:
        print("  [!] Белые списки загружены не полностью — определение будет неточным.")
    return bool(_WL_IPS or _WL_SNIS)


def load_good_list():
    """Подтверждённые вами серверы (whitelist_good.txt в Gist или рядом со скриптом)."""
    txt = None
    try:
        txt = _gist_read(WL_GOOD_FILE)
    except Exception as e:
        print(f"  Подтверждённый список: не прочитан из Gist ({e})")
    if not txt and os.path.exists(WL_GOOD_FILE):
        with open(WL_GOOD_FILE, encoding='utf-8') as f:
            txt = f.read()
    if not txt:
        return
    for u in PROTO_REGEX.findall(_decode_subscription(txt)):
        p = parse_link(u)
        if not p:
            continue
        _GOOD_IDS.add(_server_id(p))
        if _is_ip_literal(p['host']):
            with contextlib.suppress(ValueError):
                _GOOD_PREFIXES.add(_prefix24(p['host']))
        sni = (p['q'].get('sni') or '').lower()
        if sni:
            _GOOD_SNIS.add(sni)
    print(f"  Подтверждённых вами серверов: {len(_GOOD_IDS)} "
          f"({len(_GOOD_PREFIXES)} подсетей /24, {len(_GOOD_SNIS)} SNI)")


def whitelist_level(url: str) -> str:
    """'verified' — прошёл тест внутри сети с белыми списками или подтверждён вами;
    'likely' — IP и/или SNI совпали с белыми списками (правило WL_RULE); иначе 'none'."""
    if not WL_DETECT:
        return 'none'
    p = parse_link(url)
    if not p:
        return 'none'
    if _RESTRICTED_NET or _server_id(p) in _GOOD_IDS:
        return 'verified'
    host = p['host'].lower()
    ip = host if _is_ip_literal(host) else _RESOLVED.get(host)
    ip_ok = bool(ip) and ((_WL_IPS is not None and ip in _WL_IPS)
                          or _prefix24(ip) in _GOOD_PREFIXES)
    sni = ''
    if _get_security(p) in ('tls', 'reality'):
        sni = (p['q'].get('sni') or p['q'].get('host') or ('' if _is_ip_literal(host) else host)).lower()
    sni_ok = bool(sni) and (_sni_whitelisted(sni) or sni in _GOOD_SNIS)
    ok = {'both': ip_ok and sni_ok, 'ip': ip_ok, 'sni': sni_ok, 'any': ip_ok or sni_ok}[WL_RULE]
    return 'likely' if ok else 'none'


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


def _assign_names(results: list) -> collections.Counter:
    """Формирует имена: «🔑 🇩🇪 Germany #1» / «🔑 🇵🇱 Белые списки | Poland #1»
    (у серверов, проверенных внутри белых списков или вами, в конце ещё «✓»)."""
    counters: dict = {}
    levels = collections.Counter()
    for entry in results:
        url = entry[0]
        level = whitelist_level(url)
        levels[level] += 1
        wl = level != 'none'
        code, cname = _country_for(url, wl)
        flag = _iso_to_flag(code) if code else '\U0001f310'
        name = f"{flag} {WHITELIST_LABEL} | {cname}" if wl else f"{flag} {cname}"
        if NAME_NUMBERING:
            n = counters[(wl, code)] = counters.get((wl, code), 0) + 1
            name += f" #{n}"
        if level == 'verified':
            name += " \u2713"
        if NAME_SHOW_SECURITY:
            name = f"{_get_security_level(url)[1]} {name}"
        _NAMES[url] = name
    return levels


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

FAILS = collections.Counter()      # причины отказов xray-этапа
_fails_lock = threading.Lock()
_KBPS: dict = {}                   # url -> скорость в тесте передачи данных
_PROBE: dict = {}                  # url -> (ok, причина) прямого рукопожатия
_data_test_enabled = DATA_TEST
REASON_RU = {
    'xray_start': 'xray не поднялся (битый конфиг/ключи)',
    'no_https':   'HTTPS через сервер не работает',
    'mitm':       'подмена сертификата/контента',
    'hijack':     'перехват DNS/ответов на несуществующий домен',
    'google_ban': 'Google отдаёт captcha',
    'loss':       'потери выше допустимых',
    'slow':       'слишком большой пинг',
    'data_test':  'не прошёл тест передачи данных',
    'exception':  'внутренняя ошибка',
}


def _fail(reason: str):
    with _fails_lock:
        FAILS[reason] += 1


# ---------- прямая проба рукопожатия (без xray) ----------

def probe_handshake(url: str) -> tuple:
    """Для TLS/Trojan: полноценное рукопожатие с проверкой сертификата под SNI.
    Для Reality: сервер без нашего ключа обязан отдать настоящее TLS1.3-рукопожатие
    сайта-маскировки. Если не отдаёт — это не рабочий Reality (или маскировочный сайт
    у сервера мёртв). Ловит класс ошибок «TLS handshake failed» ещё до xray."""
    p = parse_link(url)
    if not p:
        return False, 'parse'
    sec = _get_security(p)
    if sec not in ('tls', 'reality'):
        return True, 'skip'
    q = p['q']
    host = p['host'].lower()
    ip = host if _is_ip_literal(host) else _RESOLVED.get(host, host)
    sni = q.get('sni') or q.get('host') or p['host']
    insecure = (q.get('allowInsecure') or q.get('insecure') or '') in ('1', 'true')

    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    if sec == 'reality' or insecure:
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
    else:
        ctx.load_default_certs()
    if sec == 'reality':
        ctx.minimum_version = ssl.TLSVersion.TLSv1_3
    alpn = q.get('alpn')
    with contextlib.suppress(Exception):
        ctx.set_alpn_protocols(alpn.split(',') if alpn else ['h2', 'http/1.1'])

    reason = 'timeout'
    for _ in range(PROBE_RETRIES):
        try:
            with socket.create_connection((ip, p['port']), timeout=PROBE_TIMEOUT) as raw:
                raw.settimeout(PROBE_TIMEOUT)
                with ctx.wrap_socket(raw, server_hostname=sni) as tls:
                    return True, tls.version() or ''
        except ssl.SSLCertVerificationError:
            return False, 'tls_cert'
        except ssl.SSLError:
            reason = 'tls_handshake'
        except (ValueError, UnicodeError):
            return False, 'bad_sni'
        except (socket.timeout, TimeoutError):
            reason = 'timeout'
        except OSError:
            reason = 'conn_reset'
    return False, reason


def _probe_blocks(url: str) -> bool:
    ok, _ = _PROBE.get(url, (True, ''))
    if ok:
        return False
    p = parse_link(url)
    return PROBE_STRICT_REALITY if p and _get_security(p) == 'reality' else PROBE_STRICT_TLS


# ---------- проверки через поднятый xray ----------

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


def _is_hijacked(session: requests.Session) -> bool:
    """Нормальный прокси на несуществующий домен отвечает ошибкой. Если пришёл
    200/204/редирект — сервер подсовывает заглушку (перехват DNS/captive-портал)."""
    host = f"probe-{os.urandom(4).hex()}.invalid"
    try:
        r = session.get(f"http://{host}/", timeout=REQUEST_TIMEOUT, allow_redirects=False)
        return r.status_code in (200, 204, 301, 302, 307, 308)
    except requests.RequestException:
        return False


def _data_test(session: requests.Session) -> tuple:
    """Скачивает DATA_TEST_BYTES байт через прокси. Ловит серверы, у которых
    рукопожатие проходит, а данные режутся/обрываются/душатся."""
    t0 = time.perf_counter()
    n = 0
    try:
        with session.get(DATA_TEST_URL, timeout=REQUEST_TIMEOUT, stream=True) as r:
            if r.status_code != 200:
                return False, 0.0
            for chunk in r.iter_content(65536):
                n += len(chunk)
                if time.perf_counter() - t0 > DATA_TEST_MAX_SEC:
                    break
    except requests.RequestException:
        return False, 0.0
    dt = max(time.perf_counter() - t0, 1e-3)
    if n < DATA_TEST_BYTES * 0.98:
        return False, 0.0
    kbps = n / 1024 / dt
    return kbps >= MIN_KBPS, kbps


def _cert_error(e: Exception) -> bool:
    return 'CERTIFICATE_VERIFY_FAILED' in str(e)


def _measure(port: int) -> tuple:
    """Возвращает ((score, avg, jitter, losses, kbps), '') либо (None, причина)."""
    session = requests.Session()
    session.trust_env = False
    session.proxies = {"http": f"http://127.0.0.1:{port}", "https": f"http://127.0.0.1:{port}"}
    session.headers['Connection'] = 'close'    # каждый раз новое соединение, как в реальном тесте клиента
    try:
        pings, losses = [], 0
        for r_i in range(PING_ROUNDS):
            k = r_i % len(HTTPS_TARGETS)
            ok = False
            for u in HTTPS_TARGETS[k:] + HTTPS_TARGETS[:k]:
                try:
                    t0 = time.perf_counter()
                    resp = session.get(u, timeout=REQUEST_TIMEOUT, allow_redirects=False)
                    ms = int((time.perf_counter() - t0) * 1000)
                    if resp.status_code == 204:
                        pings.append(ms)
                        ok = True
                        break
                    if resp.status_code == 200 and FILTER_MITM:
                        return None, 'mitm'          # 200 вместо 204 — подсунута заглушка
                except requests.exceptions.SSLError as e:
                    if FILTER_MITM and _cert_error(e):
                        return None, 'mitm'
                except requests.RequestException:
                    continue
            if not ok:
                losses += 1
            if r_i == 0 and not pings:
                return None, 'no_https'              # не тратим время на заведомо мёртвых
        if losses / PING_ROUNDS > MAX_LOSS_RATE:
            return None, 'loss'
        avg = int(statistics.median(pings))
        if avg > MAX_PING_MS:
            return None, 'slow'
        if CHECK_GOOGLE_BAN and not _check_google_ban(session):
            return None, 'google_ban'
        if HIJACK_CHECK and _is_hijacked(session):
            return None, 'hijack'
        kbps = 0.0
        if _data_test_enabled:
            ok, kbps = _data_test(session)
            if not ok:
                return None, 'data_test'
        jitter = int(statistics.stdev(pings)) if len(pings) > 1 else 0
        return (avg + jitter // 2, avg, jitter, losses, kbps), ''
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
                _fail('xray_start')
                return None
            m, reason = _measure(port)
            if m is None:
                _fail(reason)
                return None
            score, avg, jitter, losses, kbps = m
            _KBPS[url] = kbps
            return (url, score, avg, jitter, losses)
    except Exception:
        _fail('exception')
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
        all_raw.extend(found)

    seen_keys, per_endpoint, unique = set(), {}, []
    for cfg in all_raw:
        p = parse_link(cfg)
        if not p:
            continue
        key = _dedup_key(p)
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


def _get_token() -> str | None:
    token = os.environ.get('GH_TOKEN')
    if not token:
        with contextlib.suppress(Exception):
            token = subprocess.run(["gh", "auth", "token"], capture_output=True,
                                   text=True).stdout.strip()
    return token or None


def _gist_headers(token: str) -> dict:
    return {"Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28"}


def _gist_read(name: str) -> str | None:
    token = _get_token()
    if not (GID and token):
        return None
    req = url_req.Request(f"https://api.github.com/gists/{GID}", headers=_gist_headers(token))
    with url_req.urlopen(req, timeout=30) as resp:
        data = json.load(resp)
    f = data.get('files', {}).get(name)
    if not f:
        return None
    if f.get('truncated') and f.get('raw_url'):
        return requests.get(f['raw_url'], timeout=30).text
    return f.get('content')


def _gist_filenames() -> set:
    token = _get_token()
    if not (GID and token):
        return set()
    req = url_req.Request(f"https://api.github.com/gists/{GID}", headers=_gist_headers(token))
    with url_req.urlopen(req, timeout=30) as resp:
        return set(json.load(resp).get('files', {}))


def _update_gist(files: dict, delete: tuple | list = ()):
    token = _get_token()
    if not token:
        print(" Не удалось получить токен GitHub (GH_TOKEN)!")
        return
    body = {n: {"content": c} for n, c in files.items()}
    body.update({n: None for n in delete})          # null = удалить файл из Gist
    payload = json.dumps({"files": body}).encode()
    req = url_req.Request(f"https://api.github.com/gists/{GID}", data=payload, method="PATCH",
                          headers={**_gist_headers(token), "Content-Type": "application/json"})
    try:
        with url_req.urlopen(req, timeout=30) as resp:
            print(" Gist обновлён." if resp.status == 200 else f" Gist: статус {resp.status}")
    except urllib.error.HTTPError as e:
        print(f" Gist ошибка: {e.code} {e.read()[:200]!r}")
    except Exception as e:
        print(f" Gist ошибка: {e}")


# ============================================================
# ИСТОРИЯ ЗАПУСКОВ (аптайм)
# ============================================================
_HISTORY: dict = {}


def _hkey(url: str) -> str:
    p = parse_link(url)
    return hashlib.sha1(repr(_dedup_key(p)).encode()).hexdigest()[:16]


def _load_history() -> dict:
    txt = None
    try:
        txt = _gist_read(HISTORY_FILE)
    except Exception as e:
        print(f"  История: не удалось прочитать из Gist ({e})")
    if not txt and os.path.exists(HISTORY_FILE):
        with open(HISTORY_FILE, encoding='utf-8') as f:
            txt = f.read()
    try:
        data = json.loads(txt) if txt else {}
    except ValueError:
        data = {}
    return data if isinstance(data, dict) else {}


def _update_history(history: dict, candidates: list, passed: set) -> dict:
    now = int(time.time())
    for u in candidates:
        k = _hkey(u)
        rec = history.setdefault(k, {'r': [], 't': now})
        rec['r'] = (rec['r'] + [1 if k in passed else 0])[-HISTORY_RUNS:]
        rec['t'] = now
    cutoff = now - HISTORY_MAX_AGE_DAYS * 86400
    for k in [k for k, v in history.items() if v.get('t', 0) < cutoff]:
        del history[k]
    return history


def _uptime(url: str) -> float | None:
    rec = _HISTORY.get(_hkey(url))
    runs = rec['r'] if rec else []
    return sum(runs) / len(runs) if len(runs) >= MIN_HISTORY_RUNS else None


def _rank_key(entry: tuple) -> float:
    up = _uptime(entry[0])
    return entry[1] / max(up if up is not None else 0.7, 0.2)


# ============================================================
# ПРОВЕРКА ОКРУЖЕНИЯ
# ============================================================

def _reachable(session: requests.Session, url: str, want_204: bool = False) -> bool:
    try:
        r = session.get(url, timeout=8, allow_redirects=False)
        return r.status_code == 204 if want_204 else r.status_code < 500
    except requests.RequestException:
        return False


def _baseline_check() -> bool:
    """Прямые запросы к целям проверки. Заодно определяет, не запущен ли скрипт
    внутри сети с белыми списками: российские сайты доступны, зарубежные — нет."""
    global _data_test_enabled, _RESTRICTED_NET
    s = requests.Session()
    s.trust_env = False
    good = [u for u in HTTPS_TARGETS if _reachable(s, u, want_204=True)]
    if not good:
        ru_ok = any(_reachable(s, u) for u in RU_CONTROL_URLS)
        if not ru_ok:
            print("  [!] Нет прямого доступа ни к зарубежным, ни к российским целям — проверка невозможна.")
            return False
        _RESTRICTED_NET = True
        print("  [WL] Обнаружена сеть с БЕЛЫМИ СПИСКАМИ: зарубежные сайты напрямую недоступны,")
        print("       российские — доступны. Все серверы, прошедшие тест отсюда, помечаются как ПРОВЕРЕННЫЕ (✓).")
        return True
    HTTPS_TARGETS[:] = good
    if _data_test_enabled:
        ok = False
        try:
            r = s.get(DATA_TEST_URL, timeout=15)
            ok = r.status_code == 200 and len(r.content) >= DATA_TEST_BYTES * 0.98
        except requests.RequestException:
            pass
        if not ok:
            print("  [!] Тест передачи данных недоступен напрямую — отключён на этот запуск.")
            _data_test_enabled = False
    print(f"  Цели проверки: {len(HTTPS_TARGETS)} HTTPS, тест данных: {'ВКЛ' if _data_test_enabled else 'ВЫКЛ'}")
    return True


# ============================================================
# ГЛАВНЫЙ ЗАПУСК
# ============================================================

def _run_xray_stage(urls: list, label: str) -> list:
    results, total = [], len(urls)
    with cf.ThreadPoolExecutor(max_workers=XRAY_WORKERS) as ex:
        for n, res in enumerate(ex.map(test_via_xray, urls), 1):
            if res:
                results.append(res)
            if n % 25 == 0 or n == total:
                print(f"  {label}: {n}/{total}  |  прошли: {len(results)}")
    return results


def _print_fails(title: str, counter: collections.Counter):
    if not counter:
        return
    print(f"  {title}:")
    for reason, k in counter.most_common():
        print(f"    {k:>4}  {REASON_RU.get(reason, reason)}")


def run():
    t_start = time.time()

    if shutil.which(XRAY_BIN) is None:
        raise SystemExit(f"Не найден бинарник xray ('{XRAY_BIN}'). Установите его или задайте XRAY_BIN.")
    ver = subprocess.run([XRAY_BIN, 'version'], capture_output=True, text=True).stdout.splitlines()

    print("=" * 60)
    print("  VPN SCOUT 3.0")
    print(f"  {ver[0] if ver else 'xray: версия неизвестна'}")
    print(f"  xray: {XRAY_WORKERS} воркеров, раундов {PING_ROUNDS}, макс. пинг {MAX_PING_MS}мс")
    print(f"  Белые списки: определение {'ВКЛ, правило ' + WL_RULE if WL_DETECT else 'ВЫКЛ'}")
    print(f"  Проба рукопожатия: {'ВКЛ' if PROBE_HANDSHAKE else 'ВЫКЛ'} | "
          f"подтверждающий проход: {'ВКЛ' if CONFIRM_PASS else 'ВЫКЛ'} | "
          f"цепочка через РФ: {'ВКЛ' if CHAIN_PROXY else 'ВЫКЛ'}")
    print("=" * 60)

    _init_geoip()
    if not _baseline_check():
        return
    if WL_DETECT and not _RESTRICTED_NET:
        print("\n[WL] Загрузка белых списков операторов...")
        load_whitelist_db()
    if WL_DETECT:
        load_good_list()

    print("\n[1/7] Сбор конфигов...")
    configs = fetch_configs()
    print(f"      Уникальных серверов (без дублей по fp; до {MAX_PER_ENDPOINT} вариантов на host:port): {len(configs)}")
    if not configs:
        print("Нет кандидатов.")
        return

    configs, cnt = _static_filter(configs)
    print(f"[2/7] Статические фильтры: осталось {len(configs)} "
          f"(небезоп.: {cnt['insecure']}, TLS-only: {cnt['lock']}, pbk/sid: {cnt['pbk']}, "
          f"неподдерж.: {cnt['bad']})")
    candidates = list(configs)

    print(f"\n[3/7] TCP-проверка ({TCP_WORKERS} воркеров)...")
    with cf.ThreadPoolExecutor(max_workers=TCP_WORKERS) as ex:
        alive = [r for r in ex.map(tcp_alive, configs) if r]
    print(f"      TCP живых: {len(alive)} / {len(configs)}  ({int(time.time() - t_start)}с)")
    if not alive:
        print("Нет живых серверов после TCP-проверки.")
        return

    if FILTER_RUSSIAN and not CHAIN_PROXY:
        before = len(alive)
        alive = [u for u in alive
                 if not _is_russian_server(parse_link(u)['host'], u) or whitelist_level(u) != 'none']
        print(f"      Российских отброшено до xray: {before - len(alive)}")

    if PROBE_HANDSHAKE:
        print(f"\n[4/7] Прямая проба TLS/Reality-рукопожатия ({len(alive)} серверов)...")
        with cf.ThreadPoolExecutor(max_workers=TCP_WORKERS) as ex:
            probes = list(ex.map(probe_handshake, alive))
        keep, dropped, shadow = [], collections.Counter(), collections.Counter()
        for u, (ok, why) in zip(alive, probes):
            _PROBE[u] = (ok, why)
            if not ok and _probe_blocks(u):
                dropped[why] += 1
                continue
            if not ok:
                shadow[why] += 1
            keep.append(u)
        print(f"      Отсеяно пробой: {sum(dropped.values())}  {dict(dropped) if dropped else ''}")
        if shadow:
            print(f"      Провалили пробу, но пропущены (нестрогий режим): {sum(shadow.values())}  {dict(shadow)}")
        alive = keep
    else:
        print("\n[4/7] Проба рукопожатия отключена.")
    if not alive:
        print("Нет серверов после пробы.")
        return

    print(f"\n[5/7] xray-проверка {len(alive)} серверов (HTTPS, перехват, передача данных)...")
    results = _run_xray_stage(alive, "xray")
    _print_fails("Причины отказов", FAILS)
    shadow_urls = [u for u in alive if not _PROBE.get(u, (True, ''))[0]]
    if shadow_urls:
        passed_urls = {r[0] for r in results}
        print(f"  Калибровка пробы: из {len(shadow_urls)} «проваливших» пробу xray прошли "
              f"{sum(1 for u in shadow_urls if u in passed_urls)}")
    if not results:
        print("Нет рабочих серверов.")
        return

    if CONFIRM_PASS:
        print(f"\n[6/7] Подтверждающий проход через {CONFIRM_DELAY}с ({len(results)} серверов)...")
        time.sleep(CONFIRM_DELAY)
        first = {r[0]: r for r in results}
        FAILS.clear()
        second = _run_xray_stage(list(first), "подтверждение")
        merged = []
        for r in second:
            a = first[r[0]]
            merged.append((r[0], (a[1] + r[1]) // 2, (a[2] + r[2]) // 2,
                           max(a[3], r[3]), max(a[4], r[4])))
        print(f"      Не подтвердились (мигают): {len(first) - len(merged)}")
        results = merged
        if not results:
            print("Нет подтверждённых серверов.")
            return
    else:
        print("\n[6/7] Подтверждающий проход отключён.")

    print("\n[7/7] История, постобработка и сохранение...")
    history = _load_history()
    if len(results) >= 5:                      # защита: сбой раннера не должен «убить» историю
        history = _update_history(history, candidates, {_hkey(r[0]) for r in results})
    _HISTORY.clear()
    _HISTORY.update(history)
    before = len(results)
    results = [r for r in results
               if (_uptime(r[0]) is None or _uptime(r[0]) >= MIN_UPTIME)]
    if before != len(results):
        print(f"      Отсеяно по аптайму (<{int(MIN_UPTIME * 100)}% за последние запуски): {before - len(results)}")

    # Сервер с российским IP, но определённый как «белые списки», — это как раз то, что нужно
    # в основной подписке (вход в белом списке, выход за рубеж), поэтому он НЕ уходит в РФ-пул.
    ru_geo, ru_pool, intl_pool = [], [], []
    for e in results:
        is_ru = _is_russian_server(parse_link(e[0])['host'], e[0])
        if is_ru:
            ru_geo.append(e)
        (ru_pool if is_ru and whitelist_level(e[0]) == 'none' else intl_pool).append(e)

    ru_geo_urls = {e[0] for e in ru_geo}
    if CHAIN_PROXY and ru_geo and intl_pool:
        _chain_ru_urls[:] = [e[0] for e in sorted(ru_geo, key=_rank_key)[:CHAIN_TOP_N]
                             if parse_link(e[0])['proto'] in ('vless', 'trojan', 'ss')]
        targets = [e[0] for e in intl_pool if e[0] not in ru_geo_urls]
        print(f"  Цепочка: перепроверяем {len(targets)} зарубежных через {len(_chain_ru_urls)} РФ-входов...")
        chained = []
        with cf.ThreadPoolExecutor(max_workers=XRAY_WORKERS) as ex:
            for n, res in enumerate(ex.map(_test_via_chain, targets), 1):
                if res:
                    chained.append(res)
                if n % 25 == 0 or n == len(targets):
                    print(f"  Цепочка: {n}/{len(targets)}  |  прошли: {len(chained)}")
        intl_pool = chained + [e for e in intl_pool if e[0] in ru_geo_urls]
    elif CHAIN_PROXY:
        print("  Цепочка пропущена: нет российских или зарубежных серверов.")

    if FILTER_RUSSIAN:
        ru_pool = []

    if FILTER_DEAD_SNI:
        uniq = list({e[0] for e in intl_pool + ru_pool})
        with cf.ThreadPoolExecutor(max_workers=30) as ex:
            list(ex.map(_check_sni, uniq))
        intl_pool = [e for e in intl_pool if _check_sni(e[0])]
        ru_pool   = [e for e in ru_pool   if _check_sni(e[0])]

    intl_results = sorted(intl_pool, key=_rank_key)[:TOP_N_EACH]
    ru_results   = sorted(ru_pool,   key=_rank_key)[:TOP_N_EACH]
    lv_i = _assign_names(intl_results)
    lv_r = _assign_names(ru_results)
    for title, lv, n in (("зарубежные", lv_i, len(intl_results)), ("российские", lv_r, len(ru_results))):
        print(f"  Белые списки, {title}: проверено ✓ {lv['verified']}, по спискам IP/SNI {lv['likely']}, "
              f"не определены {lv['none']}  (из {n})")
    elapsed = int(time.time() - t_start)

    print(f"\n{'─' * 60}")
    print(f"  Зарубежных: {len(intl_results)}   Российских: {len(ru_results)}   Время: {elapsed}с")
    print(f"{'─' * 60}")
    for i, (url, _s, avg, jitter, losses) in enumerate(intl_results[:10], 1):
        up = _uptime(url)
        print(f"  {i:<3}{avg:>5}мс  {_KBPS.get(url, 0):>5.0f}КБ/с  "
              f"аптайм:{'—' if up is None else f'{up:.0%}':>5}  {_NAMES.get(url, '')}")

    _print_breakdown(intl_results + ru_results)

    if not intl_results:
        print("Зарубежных серверов после фильтров нет — файлы не перезаписываются.")
        return

    vps_text = "\n".join(_tagged_url(r[0]) for r in intl_results)
    sub_text = base64.b64encode(vps_text.encode("utf-8")).decode("ascii")

    files = {FILE_NAME: vps_text, SUB_FILE: sub_text,
             HISTORY_FILE: json.dumps(history, separators=(',', ':'))}
    if PUBLISH_RU_FILES and ru_results:
        ru_text = "\n".join(_tagged_url(r[0]) for r in ru_results)
        files[RU_FILE] = ru_text
        files[RU_SUB_FILE] = base64.b64encode(ru_text.encode("utf-8")).decode("ascii")
    for name, content in files.items():
        with open(name, "w", encoding="utf-8") as f:
            f.write(content)
    print(f"\n Сохранено: {FILE_NAME} ({len(intl_results)}), {SUB_FILE}, {HISTORY_FILE}")

    if GID:
        print("Обновляем Gist...")
        stale = []
        with contextlib.suppress(Exception):
            stale = [n for n in OBSOLETE_GIST_FILES if n in _gist_filenames()]
        _update_gist(files, delete=stale)
        if stale:
            print(f" Удалены устаревшие файлы из Gist: {', '.join(stale)}")
    else:
        print("  MY_GIST_ID не задан.")


if __name__ == "__main__":
    run()