import requests, os, re, subprocess, json, time, concurrent.futures
import urllib.parse, queue, socket, statistics, base64, urllib.request as url_req
import ssl

# ============================================================
# НАСТРОЙКИ
# ============================================================
GID         = os.environ.get('MY_GIST_ID')
FILE_NAME   = "vps.txt"
SUB_FILE    = "sub.txt"
VIEWER_FILE = "index.html"
XRAY_BIN    = "xray"
TOP_N_EACH  = 900

# Путь к базе GeoLite2 (скачивается в workflow)
GEOIP_DB_PATH = os.environ.get('GEOIP_DB', 'GeoLite2-Country.mmdb')

# ============================================================
# ФИЛЬТРЫ СЕРВЕРОВ
# ============================================================
on  = True
off = False

FILTER_INSECURE    = on    # on = скрыть ⚠️  небезопасные (нет TLS / allowInsecure=1)
FILTER_LOCK        = off   # on = скрыть 🔒  обычный TLS  (оставить только Reality 🔑)
FILTER_RUSSIAN     = off   # on = скрыть 🇷🇺  российские  (IP + домен + тег + SNI)
FILTER_INVALID_PBK = on    # on = скрыть серверы с невалидным pbk ключом Reality
FILTER_DEAD_SNI    = on    # on = скрыть серверы у которых SNI-сайт не отвечает

SNI_CHECK_TIMEOUT  = 4.0

# ============================================================
# ЦЕПОЧКА ЧЕРЕЗ РОССИЙСКИЕ СЕРВЕРЫ (chain proxy)
# ============================================================
CHAIN_PROXY = off
CHAIN_TOP_N = 8

# Этап 1
TCP_WORKERS    = 100
TCP_TIMEOUT    = 1.5

# Этап 2
_slow = os.environ.get('MY_SLOW_NET') == '1'
XRAY_WORKERS       = 25
PING_ROUNDS        = 2
MAX_PING_MS        = 6000  if _slow else 4000
MAX_LOSS_RATE      = 0.67  if _slow else 0.5
REQUEST_TIMEOUT    = 12.0  if _slow else 7.0
XRAY_START_TIMEOUT = 5.0   if _slow else 3.5

TEST_URLS = [
    "http://www.instagram.com/",
    "http://www.facebook.com/",
    "http://www.gstatic.com/generate_204",
    "http://cp.cloudflare.com/",
]

SOURCES = [
    "https://gist.github.com/dekinikis-tech/066c60c512b71c90a07613e8663a720c/raw/vps.tx", #Добавить t чтобы работала ссылка 
    "https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/refs/heads/main/BLACK_VLESS_RUS.txt",
    "https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/refs/heads/main/BLACK_VLESS_RUS_mobile.txt",
    "https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/refs/heads/main/BLACK_SS+All_RUS.txt",
    "https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/refs/heads/main/WHITE-CIDR-RU-all.txt",
    "https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/refs/heads/main/WHITE-CIDR-RU-checked.txt",
    "https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/refs/heads/main/WHITE-SNI-RU-all.txt",
    "https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/refs/heads/main/Vless-Reality-White-Lists-Rus-Mobile.txt",
    "https://raw.githubusercontent.com/igareck/vpn-configs-for-russia/refs/heads/main/BLACK_SS%2BAll_RUS.txt",
]


BLACK_LIST = [
    'meshky', '4mohsen', 'white', '708087',
    'oneclick', '4jadi', '4kian', 'yandex.net', 'vk-apps.com',
]

BLOCKED_IPS = (
    '104.', '172.64.', '172.65.', '172.66.', '172.67.',
    '188.114.', '162.159.', '108.162.', '158.160.',
    '51.250.', '84.201.',
)

VLESS_REGEX = re.compile(
    r"vless://(?P<uuid>[^@]+)@(?P<host>[^:?#]+):(?P<port>\d+)\??(?P<query>[^#]+)?#?(?P<n>.*)?"
)

PROTO_REGEX = re.compile(
    r'(?:vless|trojan|hysteria2|ss)://[^\s\'"<>]+'
)

port_queue: queue.Queue = queue.Queue()
for _p in range(25000, 25000 + XRAY_WORKERS):
    port_queue.put(_p)

# Очередь портов для цепочки (отдельная, чтобы не пересекаться с основными)
chain_port_queue: queue.Queue = queue.Queue()
for _p in range(20000, 20000 + 200):
    chain_port_queue.put(_p)


# ============================================================
# ГЕОЛОКАЦИЯ — GeoIP2 (geoip2) + fallback на домен/тег
# ============================================================

RU_TAG_KEYWORDS = (
    'russia', 'russian', 'россия', 'рф', '\U0001f1f7\U0001f1fa',
    '%f0%9f%87%b7%f0%9f%87%ba',
)

RU_SNI_KEYWORDS = (
    'ozone.ru', 'vk.com', 'vk-apps', 'x5.ru', 'max.ru',
    'firstvideocdn.ru', 'eh.vk', 'mail.ru', 'yandex.',
    'sber.', 'gosuslugi.', 'mos.ru', 'rmp-inc',
)

RU_DOMAIN_KEYWORDS = (
    '.ru', '.su', 'yandex', 'vk.com', 'vk-apps', 'mail.ru',
    'selectel', 'beget', 'reg.ru', 'timeweb', 'hetzner.ru',
    'serverius', 'aeza.net', 'aeza.ru',
)

# Инициализируем geoip2 reader один раз при старте
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
        print(f"  GeoIP: не удалось загрузить базу ({e}) — используем только домен/тег")

def _geoip_is_russia(ip: str) -> bool | None:
    """Возвращает True если IP российский, False если нет, None если не удалось определить."""
    if _geoip_reader is None:
        return None
    try:
        resp = _geoip_reader.country(ip)
        return resp.country.iso_code == 'RU'
    except Exception:
        return None


def _is_russian_server(address: str, url: str = '') -> bool:
    # 1. GeoIP по IP-адресу (основной метод)
    if address and address[0].isdigit():
        result = _geoip_is_russia(address)
        if result is not None:
            return result
        # geoip не смог определить — продолжаем fallback

    # 2. Fallback: домен
    addr_lower = address.lower()
    if any(kw in addr_lower for kw in RU_DOMAIN_KEYWORDS):
        return True

    # 3. Fallback: тег и SNI в URL
    if url:
        if '#' in url:
            tag_raw     = url.split('#', 1)[1].lower()
            tag_decoded = urllib.parse.unquote(tag_raw).lower()
            if any(kw in tag_raw for kw in RU_TAG_KEYWORDS):
                return True
            if any(kw in tag_decoded for kw in RU_TAG_KEYWORDS):
                return True
        sni_match = re.search(r'[?&]sni=([^&#+]+)', url.lower())
        if sni_match:
            sni = urllib.parse.unquote(sni_match.group(1))
            if any(kw in sni for kw in RU_SNI_KEYWORDS):
                return True

    return False


# ============================================================
# БЕЗОПАСНОСТЬ
# ============================================================

def _get_proto(url: str) -> str:
    for p in ('vless', 'trojan', 'hysteria2', 'ss'):
        if url.startswith(p + '://'):
            return p.upper()
    return 'UNKNOWN'


def _get_security(url: str) -> str:
    m = re.search(r'[?&]security=([^&#+]+)', url)
    if m:
        return m.group(1)
    if 'trojan://' in url:
        return 'tls'
    return 'none'


def _get_network(url: str) -> str:
    m = re.search(r'[?&]type=([^&#+]+)', url)
    return m.group(1) if m else 'tcp'


def _get_security_level(url: str) -> tuple:
    sec            = _get_security(url)
    allow_insecure = bool(re.search(r'[?&]allowInsecure=1', url))
    if sec == 'reality':
        return 'reality', '\U0001f511', 'Reality/XTLS — максимальная защита'
    if sec == 'tls' and not allow_insecure:
        return 'secure', '\U0001f512', 'TLS — соединение защищено'
    return 'insecure', '\u26a0\ufe0f', 'Небезопасно: нет TLS или allowInsecure=1'


# ============================================================
# ПРОВЕРКА PBK И SNI
# ============================================================

def _check_pbk(url: str) -> bool:
    sec = _get_security(url)
    if sec != 'reality':
        return True
    m = re.search(r'[?&]pbk=([^&#+]+)', url)
    if not m:
        return False
    pbk = urllib.parse.unquote(m.group(1)).strip()
    if len(pbk) != 43:
        return False
    if not re.fullmatch(r'[A-Za-z0-9\-_]+', pbk):
        return False
    return True


_sni_cache: dict = {}

def _check_sni(url: str) -> bool:
    """
    Проверяет SNI через реальный TLS-хендшейк (не просто TCP-пинг).
    Убеждаемся что сертификат выдан именно для этого hostname.
    """
    m = re.search(r'[?&]sni=([^&#+]+)', url)
    if not m:
        return True
    sni = urllib.parse.unquote(m.group(1)).strip().lower()
    if not sni:
        return True
    if sni in _sni_cache:
        return _sni_cache[sni]
    try:
        ctx = ssl.create_default_context()
        ctx.check_hostname = True
        ctx.verify_mode    = ssl.CERT_REQUIRED
        raw = socket.create_connection((sni, 443), timeout=SNI_CHECK_TIMEOUT)
        tls = ctx.wrap_socket(raw, server_hostname=sni)
        tls.close()
        _sni_cache[sni] = True
        return True
    except ssl.SSLCertVerificationError:
        # Порт открыт, но сертификат не тот — именно это мы и хотели поймать
        _sni_cache[sni] = False
        return False
    except Exception:
        # Таймаут, connection refused и т.д. — SNI мёртв
        _sni_cache[sni] = False
        return False


# ============================================================
# ЦЕПОЧКА ЧЕРЕЗ РОССИЙСКИЕ СЕРВЕРЫ
# ============================================================

_chain_socks_ports: list = []   # SOCKS5 порты российских прокси
_chain_procs:       list = []   # процессы xray российских прокси


def _build_socks_chain_config(data: dict, socks_port: int) -> dict:
    """Строит xray конфиг для российского сервера с SOCKS5 inbound."""
    address     = data['host']
    server_port = int(data['port'])
    query       = urllib.parse.parse_qs(data.get('query') or '')

    def q(k, d=""):
        return query.get(k, [d])[0]

    sni    = q('sni', q('host', address))
    net    = q('type', 'tcp')
    sec    = q('security', 'none')
    stream: dict = {"network": net, "security": sec}

    if net == "ws":
        stream["wsSettings"] = {
            "path": q("path", "/"),
            "headers": {"Host": q('host', address)},
        }
    elif net == "grpc":
        stream["grpcSettings"] = {"serviceName": q("serviceName", "")}
    elif net == "h2":
        stream["httpSettings"] = {
            "host": [q('host', address)],
            "path": q("path", "/"),
        }

    if sec == "reality":
        stream["realitySettings"] = {
            "serverName":  sni,
            "fingerprint": q("fp", "chrome"),
            "publicKey":   q("pbk"),
            "shortId":     q("sid"),
            "spiderX":     q("spx", "/"),
        }
    elif sec == "tls":
        stream["tlsSettings"] = {
            "serverName":  sni,
            "fingerprint": q("fp", "chrome"),
            "alpn":        ["h2", "http/1.1"],
        }

    return {
        "log": {"loglevel": "none"},
        "inbounds": [{
            "listen":   "127.0.0.1",
            "port":     socks_port,
            "protocol": "socks",
            "settings": {"auth": "noauth", "udp": False},
        }],
        "outbounds": [
            {
                "tag":      "proxy",
                "protocol": "vless",
                "settings": {
                    "vnext": [{
                        "address": address,
                        "port":    server_port,
                        "users":   [{"id": data['uuid'], "encryption": "none", "flow": q("flow")}],
                    }]
                },
                "streamSettings": stream,
            },
            {"tag": "direct", "protocol": "freedom"},
        ],
        "routing": {
            "domainStrategy": "AsIs",
            "rules": [{"type": "field", "outboundTag": "proxy", "network": "tcp,udp"}],
        }
    }


def _build_chain_test_config(target_url: str, socks_port: int, local_http_port: int) -> dict | None:
    """
    Строит xray конфиг для проверки зарубежного сервера через российский SOCKS5 прокси.
    Схема: local HTTP → зарубежный сервер → (через SOCKS5 российского прокси)
    """
    match = VLESS_REGEX.match(target_url)
    if not match:
        return None

    data        = match.groupdict()
    address     = data['host']
    server_port = int(data['port'])
    query       = urllib.parse.parse_qs(data.get('query') or '')

    def q(k, d=""):
        return query.get(k, [d])[0]

    sni    = q('sni', q('host', address))
    net    = q('type', 'tcp')
    sec    = q('security', 'none')
    stream: dict = {"network": net, "security": sec}

    if net == "ws":
        stream["wsSettings"] = {
            "path": q("path", "/"),
            "headers": {"Host": q('host', address)},
        }
    elif net == "grpc":
        stream["grpcSettings"] = {"serviceName": q("serviceName", "")}
    elif net == "h2":
        stream["httpSettings"] = {
            "host": [q('host', address)],
            "path": q("path", "/"),
        }

    if sec == "reality":
        stream["realitySettings"] = {
            "serverName":  sni,
            "fingerprint": q("fp", "chrome"),
            "publicKey":   q("pbk"),
            "shortId":     q("sid"),
            "spiderX":     q("spx", "/"),
        }
    elif sec == "tls":
        stream["tlsSettings"] = {
            "serverName":  sni,
            "fingerprint": q("fp", "chrome"),
            "alpn":        ["h2", "http/1.1"],
        }

    # Ключевое — proxySettings: направляем трафик через российский SOCKS5
    stream["proxySettings"] = {
        "tag":            "ru-proxy",
        "transportLayer": True,
    }

    return {
        "log": {"loglevel": "none"},
        "inbounds": [{
            "listen":   "127.0.0.1",
            "port":     local_http_port,
            "protocol": "http",
        }],
        "outbounds": [
            {
                "tag":             "foreign",
                "protocol":        "vless",
                "settings": {
                    "vnext": [{
                        "address": address,
                        "port":    server_port,
                        "users":   [{"id": data['uuid'], "encryption": "none", "flow": q("flow")}],
                    }]
                },
                "streamSettings": stream,
            },
            {
                "tag":      "ru-proxy",
                "protocol": "socks",
                "settings": {
                    "servers": [{
                        "address": "127.0.0.1",
                        "port":    socks_port,
                    }]
                },
            },
            {"tag": "direct", "protocol": "freedom"},
        ],
        "routing": {
            "domainStrategy": "AsIs",
            "rules": [{"type": "field", "outboundTag": "foreign", "network": "tcp,udp"}],
        }
    }


def _start_chain_proxies(ru_results: list) -> bool:
    """Запускает топ-N российских серверов как SOCKS5 прокси."""
    global _chain_socks_ports, _chain_procs
    _chain_socks_ports = []
    _chain_procs       = []

    candidates = ru_results[:CHAIN_TOP_N]
    base_port  = 19900

    for i, (url, *_) in enumerate(candidates):
        parsed = VLESS_REGEX.match(url)
        if not parsed:
            continue

        socks_port = base_port + i
        cfg        = _build_socks_chain_config(parsed.groupdict(), socks_port)
        cfg_path   = f"/tmp/chain_ru_{i}.json"

        with open(cfg_path, 'w') as f:
            json.dump(cfg, f)

        try:
            proc = subprocess.Popen(
                [XRAY_BIN, 'run', '-c', cfg_path],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
            if _wait_for_port('127.0.0.1', socks_port, 5.0):
                _chain_socks_ports.append(socks_port)
                _chain_procs.append(proc)
                print(f"  Цепочка [{i+1}] запущена на SOCKS5 порту {socks_port}")
            else:
                proc.kill()
        except Exception as e:
            print(f"  Цепочка [{i+1}] не запустилась: {e}")

    return len(_chain_socks_ports) > 0


def _stop_chain_proxies():
    """Останавливает все xray процессы цепочки."""
    for proc in _chain_procs:
        try:
            proc.kill()
        except Exception:
            pass
    _chain_procs.clear()
    _chain_socks_ports.clear()


def _test_via_chain(url: str) -> tuple | None:
    """
    Проверяет зарубежный сервер через российский SOCKS5 прокси.
    Для каждого российского прокси запускает отдельный xray с proxySettings,
    делает HTTP запрос и меряет пинг. Берёт лучший результат.
    """
    if not _chain_socks_ports or not url.startswith('vless://'):
        return None

    best = None

    for socks_port in _chain_socks_ports:
        local_port = chain_port_queue.get()
        cfg        = _build_chain_test_config(url, socks_port, local_port)
        if cfg is None:
            chain_port_queue.put(local_port)
            continue

        cfg_path = f"/tmp/chain_test_{local_port}.json"
        proc     = None

        try:
            with open(cfg_path, 'w') as f:
                json.dump(cfg, f)

            proc = subprocess.Popen(
                [XRAY_BIN, 'run', '-c', cfg_path],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )

            if not _wait_for_port('127.0.0.1', local_port, XRAY_START_TIMEOUT):
                continue

            proxies = {
                'http':  f'http://127.0.0.1:{local_port}',
                'https': f'http://127.0.0.1:{local_port}',
            }
            session           = requests.Session()
            session.trust_env = False
            session.proxies   = proxies

            pings = []
            for test_url in TEST_URLS[:2]:
                try:
                    t0 = time.perf_counter()
                    r  = session.get(test_url, timeout=REQUEST_TIMEOUT, allow_redirects=True)
                    if r.status_code in (200, 204, 301, 302):
                        pings.append(int((time.perf_counter() - t0) * 1000))
                except Exception:
                    pass

            if pings:
                avg    = int(statistics.mean(pings))
                jitter = int(statistics.stdev(pings)) if len(pings) > 1 else 0
                score  = avg + jitter // 2
                result = (url, score, avg, jitter, 0)
                if best is None or avg < best[2]:
                    best = result

        except Exception:
            pass
        finally:
            if proc:
                try:
                    proc.terminate()
                    proc.wait(timeout=1.5)
                except Exception:
                    try:
                        proc.kill()
                    except Exception:
                        pass
            if os.path.exists(cfg_path):
                os.remove(cfg_path)
            chain_port_queue.put(local_port)

    return best


# ============================================================
# ЭТАП 1: БЫСТРАЯ TCP-ПРОВЕРКА
# ============================================================

def _is_ipv6_address(host: str) -> bool:
    return ':' in host or (host.startswith('[') and host.endswith(']'))


def _extract_host_port(url: str):
    for pattern in (
        r'(?:vless|trojan)://[^@]+@([^:/?#\[\]]+|\[[^\]]+\]):(\d+)',
        r'hysteria2://[^@]+@([^:/?#\[\]]+|\[[^\]]+\]):(\d+)',
        r'ss://[^@]+@([^:/?#\[\]]+|\[[^\]]+\]):(\d+)',
    ):
        m = re.match(pattern, url)
        if m:
            return m.group(1).strip('[]'), int(m.group(2))
    return None, None


def tcp_alive(url: str):
    address, port = _extract_host_port(url)
    if address is None:
        return None
    if len(address) > 253:
        return None
    if _is_ipv6_address(address):
        return None
    if address.startswith(BLOCKED_IPS):
        return None
    addr_lower = address.lower()
    if any(bad in addr_lower for bad in BLACK_LIST):
        return None
    try:
        with socket.create_connection((address, port), timeout=TCP_TIMEOUT):
            return url
    except (OSError, UnicodeError, ValueError):
        return None


# ============================================================
# ЭТАП 2: ГЛУБОКАЯ ПРОВЕРКА ЧЕРЕЗ XRAY
# ============================================================

def _wait_for_port(host: str, port: int, timeout: float) -> bool:
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            with socket.create_connection((host, port), timeout=0.2):
                return True
        except OSError:
            time.sleep(0.05)
    return False


def _build_xray_config(data: dict, port: int) -> dict:
    address     = data['host']
    server_port = int(data['port'])
    query       = urllib.parse.parse_qs(data.get('query') or '')

    def q(k, d=""):
        return query.get(k, [d])[0]

    sni    = q('sni', q('host', address))
    net    = q('type', 'tcp')
    sec    = q('security', 'none')
    stream: dict = {"network": net, "security": sec}

    if net == "ws":
        stream["wsSettings"] = {
            "path": q("path", "/"),
            "headers": {"Host": q('host', address)},
        }
    elif net == "grpc":
        stream["grpcSettings"] = {"serviceName": q("serviceName", "")}
    elif net == "h2":
        stream["httpSettings"] = {
            "host": [q('host', address)],
            "path": q("path", "/"),
        }

    if sec == "reality":
        stream["realitySettings"] = {
            "serverName":  sni,
            "fingerprint": q("fp", "chrome"),
            "publicKey":   q("pbk"),
            "shortId":     q("sid"),
            "spiderX":     q("spx", "/"),
        }
    elif sec == "tls":
        stream["tlsSettings"] = {
            "serverName":  sni,
            "fingerprint": q("fp", "chrome"),
            "alpn":        ["h2", "http/1.1"],
        }

    return {
        "log": {"loglevel": "none"},
        "inbounds": [{"listen": "127.0.0.1", "port": port, "protocol": "http"}],
        "outbounds": [
            {
                "tag": "proxy",
                "protocol": "vless",
                "settings": {
                    "vnext": [{
                        "address": address,
                        "port":    server_port,
                        "users":   [{"id": data['uuid'], "encryption": "none", "flow": q("flow")}],
                    }]
                },
                "streamSettings": stream,
            },
            {"tag": "block", "protocol": "blackhole"}
        ],
        "routing": {
            "domainStrategy": "AsIs",
            "rules": [{"type": "field", "outboundTag": "proxy", "network": "tcp,udp"}]
        }
    }


def _build_xray_config_trojan(url: str, port: int):
    m = re.match(
        r'trojan://([^@]+)@([^:/?#\[\]]+|\[[^\]]+\]):(\d+)\??([^#]*)?#?(.*)?', url
    )
    if not m:
        return None

    password    = m.group(1)
    address     = m.group(2).strip('[]')
    server_port = int(m.group(3))
    query       = urllib.parse.parse_qs(m.group(4) or '')

    def q(k, d=""):
        return query.get(k, [d])[0]

    sni    = q('sni', address)
    net    = q('type', 'tcp')
    sec    = q('security', 'tls')
    stream: dict = {"network": net, "security": sec}

    if net == "ws":
        stream["wsSettings"] = {
            "path": urllib.parse.unquote(q("path", "/")),
            "headers": {"Host": q('host', address)},
        }
    elif net == "grpc":
        stream["grpcSettings"] = {"serviceName": q("serviceName", "")}

    if sec == "reality":
        stream["realitySettings"] = {
            "serverName":  sni,
            "fingerprint": q("fp", "chrome"),
            "publicKey":   q("pbk"),
            "shortId":     q("sid"),
            "spiderX":     q("spx", "/"),
        }
    elif sec == "tls":
        stream["tlsSettings"] = {
            "serverName":  sni,
            "fingerprint": q("fp", "chrome"),
            "allowInsecure": q("allowInsecure", "0") == "1",
            "alpn":        ["h2", "http/1.1"],
        }

    return {
        "log": {"loglevel": "none"},
        "inbounds": [{"listen": "127.0.0.1", "port": port, "protocol": "http"}],
        "outbounds": [
            {
                "tag": "proxy",
                "protocol": "trojan",
                "settings": {
                    "servers": [{"address": address, "port": server_port, "password": password}]
                },
                "streamSettings": stream,
            },
            {"tag": "block", "protocol": "blackhole"}
        ],
        "routing": {
            "domainStrategy": "AsIs",
            "rules": [{"type": "field", "outboundTag": "proxy", "network": "tcp,udp"}]
        }
    }


def _check_google_ban(session: requests.Session) -> bool:
    """
    Проверяет не заблокирован ли сервер Google-ом (captcha/sorry).
    Возвращает False ТОЛЬКО если явно получили редирект на sorry/captcha.
    В любом другом случае (ошибка, таймаут, 204, 200) — пропускаем сервер.
    Это важно: с GitHub Actions многие серверы не открывают Google
    из-за GeoIP-блокировок самого Google, но при этом работают нормально.
    """
    try:
        r = session.get(
            "http://www.google.com/generate_204",
            timeout=4.0,
            allow_redirects=False,
        )
        if r.status_code == 204:
            return True
        if r.status_code in (301, 302):
            location = r.headers.get('Location', '').lower()
            # Блокируем только явный редирект на captcha
            if 'sorry.google' in location or '/sorry/' in location:
                return False
        # Любой другой ответ (включая 403, 200, timeout) — не блокируем
        return True
    except Exception:
        # Сервер не открывает Google — это нормально, не блокируем
        return True


def test_via_xray(url: str):
    port     = port_queue.get()
    cfg_file = f"cfg_{port}.json"
    proc     = None
    try:
        if url.startswith('vless://'):
            match = VLESS_REGEX.match(url)
            if not match:
                return None
            config = _build_xray_config(match.groupdict(), port)
        elif url.startswith('trojan://'):
            config = _build_xray_config_trojan(url, port)
            if config is None:
                return None
        else:
            return (url, 9999, 9999, 0, 0)

        with open(cfg_file, "w") as f:
            json.dump(config, f)

        proc = subprocess.Popen(
            [XRAY_BIN, "run", "-c", cfg_file],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )

        if not _wait_for_port("127.0.0.1", port, XRAY_START_TIMEOUT):
            return None

        proxies = {
            "http":  f"http://127.0.0.1:{port}",
            "https": f"http://127.0.0.1:{port}",
        }
        session           = requests.Session()
        session.trust_env = False
        session.proxies   = proxies

        if not _check_google_ban(session):
            return None

        pings  = []
        losses = 0

        for _ in range(PING_ROUNDS):
            success = False
            for test_url in TEST_URLS:
                try:
                    t0      = time.perf_counter()
                    r       = session.get(test_url, timeout=REQUEST_TIMEOUT, allow_redirects=True)
                    elapsed = int((time.perf_counter() - t0) * 1000)
                    if r.status_code in (200, 204, 301, 302):
                        pings.append(elapsed)
                        success = True
                        break
                except Exception:
                    continue
            if not success:
                losses += 1

        if not pings:
            return None
        if losses / PING_ROUNDS > MAX_LOSS_RATE:
            return None

        avg_ping = int(statistics.mean(pings))
        if avg_ping > MAX_PING_MS:
            return None

        jitter = int(statistics.stdev(pings)) if len(pings) > 1 else 0
        score  = avg_ping + jitter // 2

        return (url, score, avg_ping, jitter, losses)

    except Exception:
        return None
    finally:
        if proc:
            try:
                proc.terminate()
                proc.wait(timeout=1.5)
            except Exception:
                try: proc.kill()
                except Exception: pass
        if os.path.exists(cfg_file):
            os.remove(cfg_file)
        port_queue.put(port)


# ============================================================
# СБОР КОНФИГОВ
# ============================================================

def _decode_subscription(text: str) -> str:
    stripped = text.strip()
    if re.search(r'(?:vless|trojan|hysteria2|ss)://', stripped):
        return stripped
    for variant in (stripped, stripped.replace('-', '+').replace('_', '/')):
        padded = variant + '=' * ((-len(variant)) % 4)
        try:
            decoded = base64.b64decode(padded).decode('utf-8', errors='ignore')
            if re.search(r'(?:vless|trojan|hysteria2|ss)://', decoded):
                return decoded
        except Exception:
            continue
    lines_decoded = []
    for line in stripped.splitlines():
        line = line.strip()
        if not line:
            continue
        if re.search(r'(?:vless|trojan|hysteria2|ss)://', line):
            lines_decoded.append(line)
            continue
        try:
            padded       = line + '=' * ((-len(line)) % 4)
            decoded_line = base64.b64decode(padded).decode('utf-8', errors='ignore')
            if re.search(r'(?:vless|trojan|hysteria2|ss)://', decoded_line):
                lines_decoded.append(decoded_line)
        except Exception:
            continue
    return '\n'.join(lines_decoded) if lines_decoded else stripped


def _fetch_with_retry(url: str, retries: int = 3, delay: float = 2.0):
    headers = {'User-Agent': 'Mozilla/5.0'}
    for attempt in range(1, retries + 1):
        try:
            r = requests.get(url, timeout=15, headers=headers)
            r.raise_for_status()
            return r.text
        except Exception as e:
            if attempt < retries:
                print(f"  [RETRY {attempt}/{retries}] {url}: {e}")
                time.sleep(delay)
            else:
                print(f"  [WARN] Не удалось загрузить после {retries} попыток: {url}: {e}")
    return None


def fetch_configs():
    all_raw = []
    ru_keys = set()

    for source_url in SOURCES:
        raw_text = _fetch_with_retry(source_url)
        if raw_text is None:
            continue
        text  = _decode_subscription(raw_text)
        found = PROTO_REGEX.findall(text)
        fmt   = "plain" if text is raw_text else "base64"
        print(f"  [OK] {source_url}  ->  {len(found)} конфигов  [{fmt}]")
        all_raw.extend(found)

    seen_endpoints = set()
    unique = []
    for cfg in all_raw:
        host, port = _extract_host_port(cfg)
        if host and port:
            key = f"{host}:{port}"
            if key not in seen_endpoints:
                seen_endpoints.add(key)
                unique.append(cfg)
                if _is_russian_server(host, cfg):
                    ru_keys.add(key)
        else:
            unique.append(cfg)

    return unique, ru_keys


# ============================================================
# ГЕНЕРАЦИЯ HTML
# ============================================================

def generate_html_viewer(intl_results: list, ru_results: list, elapsed: int) -> str:

    def ping_color(avg):
        if avg < 300:  return '#06d6a0'
        if avg < 1000: return '#ffd166'
        return '#ef476f'

    def make_rows(results):
        rows = []
        for i, (url, score, avg, jitter, losses) in enumerate(results, 1):
            proto    = _get_proto(url)
            security = _get_security(url)
            network  = _get_network(url)
            host, _  = _extract_host_port(url)
            tag      = urllib.parse.unquote(url.split('#')[-1])[:40] if '#' in url else (host or '')[:40]
            is_ru    = _is_russian_server(host or '', url)
            flag     = '\U0001f1f7\U0001f1fa' if is_ru else '\U0001f30d'
            loss_pct = int(losses / PING_ROUNDS * 100)
            pc       = ping_color(avg)
            safe_url = url.replace('&', '&amp;').replace('"', '&quot;').replace('<', '&lt;').replace("'", '&#39;')
            safe_tag = tag.replace('<', '&lt;').replace('>', '&gt;')

            sec_level, sec_icon, sec_tooltip = _get_security_level(url)
            if sec_level == 'reality':
                sec_color = '#a78bfa'
            elif sec_level == 'secure':
                sec_color = '#06d6a0'
            else:
                sec_color = '#ef476f'

            rows.append(
                f'<tr style="border-bottom:1px solid #1e2230">'
                f'<td style="padding:9px 10px;color:#4a5568;width:36px">{i}</td>'
                f'<td style="padding:9px 10px;max-width:200px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">{flag} {safe_tag}</td>'
                f'<td style="padding:9px 10px"><span style="background:#0d2b33;color:#00e5ff;border:1px solid #005f6b;border-radius:4px;padding:2px 7px;font-size:11px;font-weight:700">{proto}</span></td>'
                f'<td style="padding:9px 10px"><span style="background:#1a1f2e;color:#9aa0b4;border:1px solid #2a3040;border-radius:4px;padding:2px 7px;font-size:11px">{network}</span></td>'
                f'<td style="padding:9px 10px"><span style="background:#1a1f2e;color:#9aa0b4;border:1px solid #2a3040;border-radius:4px;padding:2px 7px;font-size:11px">{security}</span></td>'
                f'<td style="padding:9px 10px;text-align:center">'
                f'<span title="{sec_tooltip}" style="font-size:15px;cursor:help;color:{sec_color}">{sec_icon}</span>'
                f'</td>'
                f'<td style="padding:9px 10px;color:{pc};font-weight:700">{avg}ms</td>'
                f'<td style="padding:9px 10px;color:#718096">{jitter}ms</td>'
                f'<td style="padding:9px 10px;color:{"#06d6a0" if loss_pct==0 else "#ef476f"}">{loss_pct}%</td>'
                f'<td style="padding:9px 10px;white-space:nowrap"><button onclick="copyVpn(this)" data-url="{safe_url}" style="background:#0d2b33;border:1px solid #005f6b;color:#00e5ff;border-radius:5px;padding:4px 10px;cursor:pointer;font-size:13px;margin-right:6px">Copy</button><span class="ping-live" data-host="{host or ""}" style="font-size:12px;color:#4a5568">—</span></td>'
                f'</tr>'
            )
        return '\n'.join(rows)

    intl_rows = make_rows(intl_results)
    ru_rows   = make_rows(ru_results)
    total     = len(intl_results) + len(ru_results)
    updated   = time.strftime('%d.%m.%Y %H:%M UTC', time.gmtime())
    best_ping = min((r[2] for r in intl_results), default=0)

    return f"""<!DOCTYPE html>
<html lang="ru">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>VPN Scout</title>
<style>
body {{ margin:0; padding:0; background:#0a0c10; color:#e2e8f0; font-family:Arial,sans-serif; font-size:13px; }}
h1 {{ margin:0; padding:20px 20px 0; font-size:24px; color:#fff; }}
.info {{ padding:8px 20px 16px; color:#718096; font-size:12px; }}
.info b {{ color:#00e5ff; }}
.legend {{ padding:0 20px 10px; font-size:11px; color:#718096; display:flex; gap:16px; flex-wrap:wrap; }}
.legend span {{ display:flex; align-items:center; gap:4px; }}
.stats-row {{ display:table; width:100%; border-collapse:separate; border-spacing:10px; padding:0 10px 10px; box-sizing:border-box; }}
.stat {{ display:table-cell; background:#111318; border:1px solid #1e2230; border-radius:8px; padding:14px 18px; text-align:center; }}
.stat-num {{ font-size:26px; font-weight:700; color:#fff; }}
.stat-lbl {{ font-size:11px; color:#718096; margin-top:4px; }}
.tab-bar {{ padding:10px 20px; }}
.tab-btn {{ display:inline-block; padding:10px 30px; margin-right:8px; border-radius:8px; border:2px solid #1e2230; background:#111318; color:#e2e8f0; font-size:14px; font-weight:700; cursor:pointer; text-decoration:none; }}
.tab-btn.active-intl {{ background:#00e5ff; color:#000; border-color:#00e5ff; }}
.tab-btn.active-ru  {{ background:#ff6b35; color:#fff; border-color:#ff6b35; }}
.tab-btn:hover {{ border-color:#718096; }}
.section {{ display:none; padding:0 20px 40px; }}
.section.visible {{ display:block; }}
.tbl-wrap {{ overflow-x:auto; border:1px solid #1e2230; border-radius:8px; }}
table {{ width:100%; border-collapse:collapse; background:#111318; }}
thead th {{ background:#0d1017; color:#718096; font-size:10px; text-transform:uppercase; padding:11px 12px; text-align:left; border-bottom:1px solid #1e2230; white-space:nowrap; }}
tbody tr:hover {{ background:#161b26; }}
#toast {{ position:fixed; bottom:24px; right:24px; background:#06d6a0; color:#000; font-weight:700; font-size:13px; padding:10px 20px; border-radius:8px; opacity:0; transition:opacity .3s; pointer-events:none; z-index:999; }}
#toast.show {{ opacity:1; }}
</style>
</head>
<body>
<h1>VPN Scout</h1>
<div class="info">Обновлено: <b>{updated}</b> &nbsp;|&nbsp; Время проверки: <b>{elapsed}с</b></div>
<div class="legend">
  <span><span style="color:#a78bfa;font-size:14px">🔑</span> Reality/XTLS — максимальная защита</span>
  <span><span style="color:#06d6a0;font-size:14px">🔒</span> TLS — соединение защищено</span>
  <span><span style="color:#ef476f;font-size:14px">⚠️</span> Небезопасно (нет TLS или allowInsecure=1)</span>
</div>
<div class="stats-row">
  <div class="stat"><div class="stat-num" style="color:#00e5ff">{len(intl_results)}</div><div class="stat-lbl">🌍 Зарубежных</div></div>
  <div class="stat"><div class="stat-num" style="color:#ff6b35">{len(ru_results)}</div><div class="stat-lbl">🇷🇺 Российских</div></div>
  <div class="stat"><div class="stat-num">{total}</div><div class="stat-lbl">Всего живых</div></div>
  <div class="stat"><div class="stat-num" style="color:#06d6a0">{best_ping}ms</div><div class="stat-lbl">Лучший пинг</div></div>
</div>
<div class="tab-bar" style="display:flex;align-items:center;flex-wrap:wrap;gap:8px">
  <button class="tab-btn active-intl" id="btn-intl" onclick="showTab('intl')">🌍 Зарубежные ({len(intl_results)})</button>
  <button class="tab-btn" id="btn-ru" onclick="showTab('ru')">🇷🇺 Российские ({len(ru_results)})</button>
  <button id="btn-pingall" onclick="pingAll()" style="margin-left:auto;background:#1a1040;border:2px solid #a78bfa;color:#a78bfa;border-radius:8px;padding:10px 22px;font-size:14px;font-weight:700;cursor:pointer">
    ⚡ Проверить все с моего IP
  </button>
  <span id="ping-status" style="font-size:12px;color:#718096"></span>
</div>
<div class="section visible" id="sec-intl">
  <div class="tbl-wrap">
    <table>
      <thead><tr><th>#</th><th>Сервер</th><th>Протокол</th><th>Транспорт</th><th>Безопасность</th><th>🔒</th><th>Пинг</th><th>Jitter</th><th>Loss</th><th></th></tr></thead>
      <tbody>{intl_rows if intl_rows else '<tr><td colspan="10" style="text-align:center;padding:30px;color:#718096">Нет серверов</td></tr>'}</tbody>
    </table>
  </div>
</div>
<div class="section" id="sec-ru">
  <div class="tbl-wrap">
    <table>
      <thead><tr><th>#</th><th>Сервер</th><th>Протокол</th><th>Транспорт</th><th>Безопасность</th><th>🔒</th><th>Пинг</th><th>Jitter</th><th>Loss</th><th></th></tr></thead>
      <tbody>{ru_rows if ru_rows else '<tr><td colspan="10" style="text-align:center;padding:30px;color:#718096">Нет серверов</td></tr>'}</tbody>
    </table>
  </div>
</div>
<div id="toast">Скопировано!</div>
<script>
function showTab(name) {{
  document.getElementById('sec-intl').className = 'section' + (name === 'intl' ? ' visible' : '');
  document.getElementById('sec-ru').className   = 'section' + (name === 'ru'   ? ' visible' : '');
  document.getElementById('btn-intl').className = 'tab-btn' + (name === 'intl' ? ' active-intl' : '');
  document.getElementById('btn-ru').className   = 'tab-btn' + (name === 'ru'   ? ' active-ru'   : '');
}}
function copyVpn(btn) {{
  var url = btn.getAttribute('data-url');
  var ta = document.createElement('textarea');
  ta.value = url; ta.style.position = 'fixed'; ta.style.left = '-9999px';
  document.body.appendChild(ta); ta.select();
  try {{
    document.execCommand('copy');
    btn.textContent = 'OK!'; btn.style.color = '#06d6a0'; btn.style.borderColor = '#06d6a0';
    var t = document.getElementById('toast'); t.className = 'show';
    setTimeout(function() {{ btn.textContent = 'Copy'; btn.style.color = '#00e5ff'; btn.style.borderColor = '#005f6b'; t.className = ''; }}, 1500);
  }} catch(e) {{ alert('Не удалось скопировать'); }}
  document.body.removeChild(ta);
}}
async function pingHost(host) {{
  if (!host) return null;
  var targets = ['https://' + host + '/favicon.ico', 'https://' + host + '/robots.txt', 'https://' + host + '/'];
  for (var i = 0; i < targets.length; i++) {{
    try {{
      var t0 = performance.now();
      await fetch(targets[i], {{ mode: 'no-cors', cache: 'no-store', signal: AbortSignal.timeout(5000) }});
      return Math.round(performance.now() - t0);
    }} catch(e) {{}}
  }}
  return null;
}}
async function pingAll() {{
  var btn = document.getElementById('btn-pingall');
  var status = document.getElementById('ping-status');
  btn.disabled = true; btn.textContent = '⏳ Проверяю...'; btn.style.opacity = '0.6';
  var spans = document.querySelectorAll('.ping-live');
  var total = spans.length, done = 0;
  var BATCH = 10;
  for (var i = 0; i < spans.length; i += BATCH) {{
    var batch = Array.from(spans).slice(i, i + BATCH);
    await Promise.all(batch.map(async function(span) {{
      var host = span.getAttribute('data-host');
      span.textContent = '...'; span.style.color = '#718096';
      var ms = await pingHost(host);
      done++; status.textContent = done + '/' + total;
      if (ms === null) {{ span.textContent = '✗'; span.style.color = '#ef476f'; }}
      else if (ms < 300) {{ span.textContent = ms + 'ms'; span.style.color = '#06d6a0'; span.style.fontWeight = '700'; }}
      else if (ms < 1000) {{ span.textContent = ms + 'ms'; span.style.color = '#ffd166'; span.style.fontWeight = '700'; }}
      else {{ span.textContent = ms + 'ms'; span.style.color = '#ef476f'; span.style.fontWeight = '700'; }}
    }}));
  }}
  btn.disabled = false; btn.textContent = '🔄 Проверить снова'; btn.style.opacity = '1';
  status.textContent = '✓ Готово (' + total + ' серверов)'; status.style.color = '#06d6a0';
}}
</script>
</body>
</html>"""


# ============================================================
# ГЛАВНЫЙ ЗАПУСК
# ============================================================

def run():
    t_start = time.time()
    print("=" * 60)
    print("  ЗАПУСК ПРОВЕРКИ VPN-СЕРВЕРОВ  (2-этапный)")
    print(f"  TCP-воркеры   : {TCP_WORKERS}  (таймаут {TCP_TIMEOUT}с)")
    print(f"  Xray-воркеры  : {XRAY_WORKERS}  (таймаут {XRAY_START_TIMEOUT}с)")
    print(f"  Раундов       : {PING_ROUNDS},  макс. пинг: {MAX_PING_MS}мс")
    print(f"  Топ каждой гео: {TOP_N_EACH}")
    print(f"  Динамический таймаут (MY_SLOW_NET): {'ВКЛ' if _slow else 'ВЫКЛ'}")
    print(f"  Google-бан фильтр: ВКЛ")
    print(f"  Base64-подписка: {SUB_FILE}")
    print(f"  Фильтр ⚠️  небезопасные  : {'ВКЛ' if FILTER_INSECURE else 'ВЫКЛ'}")
    print(f"  Фильтр 🔒  TLS-only      : {'ВКЛ' if FILTER_LOCK     else 'ВЫКЛ'}")
    print(f"  Фильтр 🇷🇺  российские   : {'ВКЛ' if FILTER_RUSSIAN  else 'ВЫКЛ'}")
    print(f"  Цепочка через РФ         : {'ВКЛ (топ-' + str(CHAIN_TOP_N) + ')' if CHAIN_PROXY else 'ВЫКЛ'}")
    print(f"  GeoIP база               : {GEOIP_DB_PATH}")
    print("=" * 60)

    # Инициализируем GeoIP один раз
    _init_geoip()

    print("\n[1/4] Сбор конфигов...")
    all_configs, ru_source_keys = fetch_configs()
    print(f"      Итого уникальных (по хосту:порту): {len(all_configs)}")
    if not all_configs:
        print("Нет кандидатов.")
        return

    print(f"\n[2/4] Быстрая TCP-проверка ({TCP_WORKERS} воркеров)...")
    alive = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=TCP_WORKERS) as ex:
        for future in concurrent.futures.as_completed(
            {ex.submit(tcp_alive, u): u for u in all_configs}
        ):
            result = future.result()
            if result:
                alive.append(result)

    elapsed_tcp = int(time.time() - t_start)
    print(f"      TCP живых: {len(alive)} / {len(all_configs)}  ({elapsed_tcp}с)")
    if not alive:
        print("Нет живых серверов после TCP-проверки.")
        return
    print(f"\n[3/4] Глубокая xray-проверка {len(alive)} серверов ({XRAY_WORKERS} воркеров)...")
    results = []
    tested  = 0
    total   = len(alive)

    with concurrent.futures.ThreadPoolExecutor(max_workers=XRAY_WORKERS) as ex:
        futures = {ex.submit(test_via_xray, u): u for u in alive}
        for future in concurrent.futures.as_completed(futures):
            tested += 1
            if tested % 10 == 0 or tested == total:
                print(f"  Прогресс: {tested}/{total}  |  Прошли xray: {len(results)}")
            res = future.result()
            if res:
                results.append(res)


    print(f"\n[4/4] Сохранение...")
    if not results:
        print("Нет рабочих серверов.")
        return

    results.sort(key=lambda x: x[1])

    # ----------------------------------------------------------------
    # Помечаем каждый результат флагом is_ru один раз — используется везде
    # ----------------------------------------------------------------
    tagged = []
    for entry in results:
        h, _ = _extract_host_port(entry[0])
        is_ru = _is_russian_server(h or '', entry[0])
        tagged.append((entry, is_ru))

    ru_pool   = [e for e, is_ru in tagged if     is_ru]   # все РФ после xray
    intl_pool = [e for e, is_ru in tagged if not is_ru]   # все зарубежные после xray

    # ----------------------------------------------------------------
    # Цепочка через российские серверы
    # Логика: РФ-серверы поднимаются как SOCKS5 и используются для
    # перепроверки зарубежных с российского IP. После этого:
    #   FILTER_RUSSIAN=on  → РФ-серверы выброшены, в финал не идут
    #   FILTER_RUSSIAN=off → РФ-серверы добавляются в финал
    #                        но БЕЗ перепроверки через цепочку
    #                        (они сами и есть цепочка, тестировать их
    #                         через себя нет смысла)
    # ----------------------------------------------------------------
    if CHAIN_PROXY:
        if ru_pool:
            print(f"\n[ЦЕПОЧКА] Найдено российских серверов: {len(ru_pool)}")
            print(f"  Запускаем топ-{CHAIN_TOP_N} как SOCKS5 прокси...")
            started = _start_chain_proxies(ru_pool)

            if started:
                print(f"  Перепроверяем {len(intl_pool)} зарубежных через российскую цепочку...")
                chain_results = []
                with concurrent.futures.ThreadPoolExecutor(max_workers=XRAY_WORKERS) as ex:
                    futures = {ex.submit(_test_via_chain, e[0]): e for e in intl_pool}
                    done = 0
                    for future in concurrent.futures.as_completed(futures):
                        done += 1
                        res = future.result()
                        if res:
                            chain_results.append(res)
                        if done % 10 == 0 or done == len(intl_pool):
                            print(f"  Прогресс цепочки: {done}/{len(intl_pool)}  |  Прошли: {len(chain_results)}")

                _stop_chain_proxies()
                print(f"  Через цепочку прошли: {len(chain_results)} из {len(intl_pool)} зарубежных")
                intl_pool = chain_results  # зарубежные теперь с реальным пингом из РФ
            else:
                print("  Не удалось запустить ни один российский сервер — цепочка пропущена.")
        else:
            print("[ЦЕПОЧКА] Российских серверов не найдено — пропускаем.")

    # ----------------------------------------------------------------
    # Фильтры — применяются ко всем серверам одинаково.
    # FILTER_RUSSIAN работает корректно при любом значении CHAIN_PROXY:
    #   on  → РФ-серверы не попадают в финал
    #   off → РФ-серверы попадают в финал
    # ----------------------------------------------------------------
    def _apply_filters(pool: list, pool_is_ru: bool) -> tuple[list, dict]:
        filtered = []
        counts = {'insecure': 0, 'lock': 0, 'ru': 0, 'pbk': 0, 'sni': 0}
        for entry in pool:
            url = entry[0]
            sec_level, _, _ = _get_security_level(url)

            if FILTER_INSECURE and sec_level == 'insecure':
                counts['insecure'] += 1; continue
            if FILTER_LOCK and sec_level == 'secure':
                counts['lock'] += 1; continue
            if FILTER_RUSSIAN and pool_is_ru:
                counts['ru'] += 1; continue
            if FILTER_INVALID_PBK and not _check_pbk(url):
                counts['pbk'] += 1; continue
            if FILTER_DEAD_SNI and not _check_sni(url):
                counts['sni'] += 1; continue
            filtered.append(entry)
        return filtered, counts

    if FILTER_DEAD_SNI:
        all_for_sni = list({e[0] for e in intl_pool + ru_pool})
        print(f"  Проверка SNI-сайтов ({len(all_for_sni)} уникальных, TLS-хендшейк)...")
        with concurrent.futures.ThreadPoolExecutor(max_workers=30) as ex:
            list(ex.map(_check_sni, all_for_sni))

    intl_filtered, intl_counts = _apply_filters(intl_pool, pool_is_ru=False)
    ru_filtered,   ru_counts   = _apply_filters(ru_pool,   pool_is_ru=True)

    # Суммируем статистику фильтров
    total_before  = len(intl_pool) + len(ru_pool)
    total_after   = len(intl_filtered) + len(ru_filtered)
    cnt_insecure  = intl_counts['insecure'] + ru_counts['insecure']
    cnt_lock      = intl_counts['lock']     + ru_counts['lock']
    cnt_ru        = intl_counts['ru']       + ru_counts['ru']
    cnt_pbk       = intl_counts['pbk']      + ru_counts['pbk']
    cnt_sni       = intl_counts['sni']      + ru_counts['sni']

    if total_before != total_after:
        print(f"  Фильтры убрали: {total_before - total_after} серверов  (осталось {total_after})")
        if cnt_insecure: print(f"    ⚠️  небезопасных убрано : {cnt_insecure}")
        if cnt_lock:     print(f"    🔒 TLS-only убрано     : {cnt_lock}")
        if cnt_ru:       print(f"    🇷🇺 российских убрано  : {cnt_ru}")
        if cnt_pbk:      print(f"    🔑 невалидный pbk      : {cnt_pbk}")
        if cnt_sni:      print(f"    🌐 мёртвый SNI-сайт    : {cnt_sni}")

    intl_results = sorted(intl_filtered, key=lambda x: x[1])[:TOP_N_EACH]
    ru_results   = sorted(ru_filtered,   key=lambda x: x[1])[:TOP_N_EACH]

    elapsed_total = int(time.time() - t_start)
    print(f"\n{'─'*60}")
    print(f"  Всего: {len(all_configs)} -> TCP: {len(alive)} -> финал: {len(intl_results)}")
    print(f"  Зарубежных в топе: {len(intl_results)}")
    print(f"  Время: {elapsed_total}с")
    print(f"{'─'*60}")

    print("\n  Топ-10 зарубежных:")
    for i, (url, score, avg, jitter, losses) in enumerate(intl_results[:10], 1):
        _, sec_icon, _ = _get_security_level(url)
        name = urllib.parse.unquote(url.split('#')[-1])[:40] if '#' in url else url[8:48]
        print(f"  {i:<3} {avg:>5}мс  jitter:{jitter:>4}мс  loss:{losses}/{PING_ROUNDS}  {sec_icon} {name}")

    tagged_urls = []
    for r in intl_results:
        url = r[0]
        _, sec_icon, _ = _get_security_level(url)
        if '#' in url:
            base, tag = url.rsplit('#', 1)
            clean_tag = urllib.parse.unquote(tag)[:38]
            tagged_urls.append(f"{base}#{sec_icon} {clean_tag}")
        else:
            host, port = _extract_host_port(url)
            tagged_urls.append(f"{url}#{sec_icon} {host}:{port}")

    with open(FILE_NAME, "w", encoding="utf-8") as f:
        f.write("\n".join(tagged_urls))
    print(f"\n Сохранено {len(tagged_urls)} серверов в {FILE_NAME}")

    b64_content = base64.b64encode("\n".join(tagged_urls).encode("utf-8")).decode("utf-8")
    with open(SUB_FILE, "w", encoding="utf-8") as f:
        f.write(b64_content)
    print(f" Base64-подписка сохранена в {SUB_FILE}")

    html = generate_html_viewer(intl_results, ru_results, elapsed_total)
    with open(VIEWER_FILE, "w", encoding="utf-8") as f:
        f.write(html)
    print(f" HTML-viewer сохранён в {VIEWER_FILE}")

    if GID:
        print("Обновляем Gist (три файла: vps.txt + sub.txt + index.html)...")
        with open(FILE_NAME, "r", encoding="utf-8") as f:
            vps_content = f.read()
        with open(SUB_FILE, "r", encoding="utf-8") as f:
            sub_content = f.read()
        with open(VIEWER_FILE, "r", encoding="utf-8") as f:
            html_content = f.read()

        token = os.environ.get('GH_TOKEN')
        if not token:
            try:
                token_res = subprocess.run(["gh", "auth", "token"], capture_output=True, text=True)
                token = token_res.stdout.strip()
            except Exception:
                token = None

        if token:
            payload = json.dumps({
                "files": {
                    FILE_NAME:   {"content": vps_content},
                    SUB_FILE:    {"content": sub_content},
                    VIEWER_FILE: {"content": html_content},
                }
            }).encode("utf-8")

            req = url_req.Request(
                f"https://api.github.com/gists/{GID}",
                data=payload,
                method="PATCH",
                headers={
                    "Authorization":        f"Bearer {token}",
                    "Content-Type":         "application/json",
                    "Accept":               "application/vnd.github+json",
                    "X-GitHub-Api-Version": "2022-11-28",
                }
            )
            try:
                with url_req.urlopen(req) as resp:
                    if resp.status == 200:
                        print(" Gist обновлён.")
                    else:
                        print(f" Gist ошибка: статус {resp.status}")
            except Exception as e:
                print(f" Gist ошибка: {e}")
        else:
            print(" Не удалось получить токен GitHub (GH_TOKEN)!")
    else:
        print("  MY_GIST_ID не задан.")


if __name__ == "__main__":
    run()
#fack