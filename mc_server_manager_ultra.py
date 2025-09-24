"""
Minecraft Server Manager ULTRA
--------------------------------

App GUI (Tkinter) para crear, iniciar y administrar servidores locales de Minecraft
(Vanilla/Forge) con túneles playit.gg / joinmc.link (solo UI, sin ruido en consola),
consola en tiempo real, envío de comandos robusto (STDIN + RCON), diálogo de
configuración con **scroll**, estilos modernos y UX clara.

Mejoras integradas:
- Barra de progreso para descargas
- Detección de proceso que ocupa puertos
- Validaciones antes de iniciar servidor
- Sistema de backups del mundo
- Logs persistentes con rotación
- Mejoras en la UI de dirección pública
- Menú contextual en consola
- Seguridad RCON mejorada
- Persistencia de tamaño/posición de ventana
- Y muchas mejoras más...

Requisitos:
- Python 3.8+
- pip install requests psutil
- Java instalado (o configura la ruta en "Configurar")
- (Opcional) agente playit.gg descargado

Licencia: MIT
"""

import os
import sys
import json
import time
import queue
import shutil
import socket
import struct
import threading
import subprocess
import signal
import webbrowser
import traceback
import logging
import zipfile
import secrets
import string
from pathlib import Path
from datetime import datetime
from logging.handlers import RotatingFileHandler
import re
import xml.etree.ElementTree as ET

try:
    import tkinter as tk
    from tkinter import ttk, messagebox, filedialog
except Exception as e:
    print("Tkinter no está disponible en este entorno:", e)
    sys.exit(1)

try:
    import requests
except ImportError:
    print("Falta el paquete 'requests'. Instálalo con: pip install requests")
    sys.exit(1)

try:
    import psutil
except ImportError:
    print("Falta el paquete 'psutil'. Instálalo con: pip install psutil")
    psutil = None

# ------------------------------------------------------------------------------
# Constantes y utilidades
# ------------------------------------------------------------------------------

APP_NAME = "Minecraft Server Manager ULTRA"
APP_CONFIG_NAME = "app_config.json"
DEFAULT_DIRNAME = "MinecraftLocalServerGUI"

APP_STATE_DIR = Path.home() / DEFAULT_DIRNAME
DEFAULT_SERVER_DIR = str(Path.home() / DEFAULT_DIRNAME)

MOJANG_MANIFEST_URLS = [
    "https://piston-meta.mojang.com/mc/game/version_manifest.json",
    "https://launchermeta.mojang.com/mc/game/version_manifest.json",
]

SERVER_JAR_BASENAME = "server-{version}.jar"
SERVER_JAR_ALIAS = "server.jar"

DEFAULT_APP_CONFIG = {
    "server_dir": DEFAULT_SERVER_DIR,
    "java_path": "java",
    "mc_version": "latest-release",
    "server_type": "vanilla",        # vanilla | forge
    "forge_version": "",
    "ram_min": "1G",
    "ram_max": "2G",
    "server_port": 25565,
    "playit_path": "",
    "auto_start_playit": True,
    "console_autoscroll": True,
    "last_public_address": "",
    "tunnels_per_dir": {},           # {server_dir: "host:port"}
    "enable_jvm_optim": True,
    "enable_opt_properties": True,
    # RCON
    "enable_rcon": True,
    "rcon_port": 25575,
    "rcon_password": "minecraft",
    # Autosave
    "enable_autosave": True,
    "autosave_minutes": 10,
    # Consola
    "hide_playit_logs": True,
    # Linux/macOS: usar PTY para evitar problemas de JLine (recomendado)
    "use_pty_on_unix": True,
    # Ventana
    "window_geometry": "",
    # Filtros consola
    "hide_info_logs": False,
}

DEFAULT_SERVER_PROPERTIES = {
    "server-port": "25565",
    "online-mode": "true",
    "difficulty": "easy",
    "gamemode": "survival",
    "max-players": "10",
    "white-list": "false",
    "motd": "Servidor Minecraft (GUI)",
    "level-name": "world",
    "level-seed": "",
    "spawn-monsters": "true",
    "spawn-animals": "true",
    "allow-nether": "true",
    "pvp": "true",
    "enable-command-block": "false",
    "view-distance": "10",
    "simulation-distance": "10",
    "allow-flight": "false",
    "hardcore": "false",
    "enforce-whitelist": "false",
    "enable-status": "true",
    # RCON (se fuerza desde la app si está activo)
    "enable-rcon": "false",
    "rcon.password": "",
    "rcon.port": "25575",
    # Optimizaciones recomendadas
    "sync-chunk-writes": "false",
    "network-compression-threshold": "512",
    "max-tick-time": "60000"
}

RE_JOIN = re.compile(r":\s*([A-Za-z0-9_]{1,16})\sjoined the game")
RE_LEAVE = re.compile(r":\s*([A-Za-z0-9_]{1,16})\sleft the game")
RE_CHAT = re.compile(r"]:\s*<([A-Za-z0-9_]{1,16})>\s(.*)$")

READY_HINTS = ["Done (", 'For help, type "help" or "?"']

RE_PUBLIC_HOST = re.compile(r"([A-Za-z0-9\.\-]+\.(?:playit\.gg|joinmc\.link))(?:[: ](\d+))?")
RE_GENERIC_TCP = re.compile(r"(tcp://)?([A-Za-z0-9\.\-]+):(\d{2,5})")


def ensure_dir(path: str):
    Path(path).mkdir(parents=True, exist_ok=True)


def human_size(nbytes: int) -> str:
    step = 1024.0
    for unit in ["B", "KB", "MB", "GB", "TB"]:
        if nbytes < step:
            return f"{nbytes:.1f} {unit}"
        nbytes /= step
    return f"{nbytes:.1f} PB"


def local_ip() -> str:
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.settimeout(0.1)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        try:
            return socket.gethostbyname(socket.gethostname())
        except Exception:
            return "127.0.0.1"


def is_windows() -> bool:
    return os.name == "nt"


def timestamp() -> str:
    return datetime.now().strftime("%H:%M:%S")


def read_text_file(path: str) -> str:
    try:
        with open(path, "r", encoding="utf-8") as f:
            return f.read()
    except Exception:
        try:
            with open(path, "r", encoding="latin-1", errors="replace") as f:
                return f.read()
        except Exception:
            return ""


def write_text_file(path: str, content: str):
    ensure_dir(str(Path(path).parent))
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)


def merge_properties(original: dict, defaults: dict) -> dict:
    merged = defaults.copy()
    merged.update(original or {})
    return merged


def parse_properties(text: str) -> dict:
    props = {}
    for line in text.splitlines():
        if not line or line.strip().startswith("#"):
            continue
        if "=" in line:
            k, v = line.split("=", 1)
            props[k.strip()] = v.strip()
    return props


def render_properties(props: dict) -> str:
    lines = [
        "# Minecraft server properties",
        f"# Generated by {APP_NAME} on {datetime.now().isoformat(timespec='seconds')}",
    ]
    for k, v in props.items():
        lines.append(f"{k}={v}")
    return "\n".join(lines) + "\n"


def find_executable(candidate: str, extra_dirs=None) -> str:
    extra_dirs = extra_dirs or []
    exts = [""] if not is_windows() else [".exe", ".bat", ".cmd", ""]
    paths = os.environ.get("PATH", "").split(os.pathsep)
    for d in extra_dirs + paths:
        if not d:
            continue
        for ext in exts:
            p = Path(d) / (candidate + ext)
            if p.exists() and os.access(str(p), os.X_OK):
                return str(p)
    return ""


def is_port_free(port: int, host: str = "0.0.0.0") -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            s.bind((host, port))
            return True
        except OSError:
            return False


def who_uses_port(port: int) -> str:
    """Detecta qué proceso está usando un puerto."""
    try:
        if psutil:
            for conn in psutil.net_connections():
                if conn.laddr and conn.laddr.port == port:
                    try:
                        proc = psutil.Process(conn.pid)
                        return f"PID {conn.pid} ({proc.name()})"
                    except (psutil.NoSuchProcess, psutil.AccessDenied):
                        return f"PID {conn.pid} (proceso no accesible)"
    except Exception:
        pass
    
    # Fallback sin psutil
    try:
        if is_windows():
            cmd = ["netstat", "-ano", "-p", "tcp"]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=5)
            for line in result.stdout.splitlines():
                if f":{port}" in line and "LISTENING" in line:
                    parts = line.split()
                    if len(parts) >= 5:
                        return f"PID {parts[-1]} (netstat)"
        else:
            cmd = ["lsof", "-i", f":{port}"]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=5)
            if result.stdout:
                lines = result.stdout.strip().split('\n')
                if len(lines) > 1:
                    return lines[1][:100]
    except Exception:
        pass
    
    return "No se pudo determinar"


def wait_port_release(port: int, host: str = "0.0.0.0", timeout: float = 12.0, poll: float = 0.25) -> bool:
    """
    Espera hasta que el puerto quede libre (se pueda bindear) o expire el timeout.
    Devuelve True si quedó libre, False si siguió ocupado.
    """
    deadline = time.time() + timeout
    while time.time() < deadline:
        free_any = is_port_free(port, host=host) or is_port_free(port, host="127.0.0.1")
        if free_any:
            return True
        time.sleep(poll)
    
    # último intento
    free_now = is_port_free(port, host=host) or is_port_free(port, host="127.0.0.1")
    if not free_now:
        owner = who_uses_port(port)
        print(f"El puerto {port} parece estar ocupado por: {owner}")
    return free_now


def write_properties_file(path: str, props: dict):
    """
    Escribe server.properties en latin-1 (con reemplazo) para evitar problemas con MOTD y acentos.
    """
    ensure_dir(str(Path(path).parent))
    text = render_properties(props)
    with open(path, "w", encoding="latin-1", errors="replace") as f:
        f.write(text)


def generate_random_password(length=20):
    """Genera una contraseña aleatoria segura."""
    alphabet = string.ascii_letters + string.digits + "!@#$%^&*"
    return ''.join(secrets.choice(alphabet) for _ in range(length))


# ------------------------------------------------------------------------------
# Diálogo de progreso para descargas
# ------------------------------------------------------------------------------

class ProgressDialog(tk.Toplevel):
    def __init__(self, parent, title="Descargando", max_value=100):
        super().__init__(parent)
        self.title(title)
        self.geometry("400x120")
        self.transient(parent)
        self.grab_set()
        self.max_value = max_value
        self.var = tk.DoubleVar()
        self.var.set(0)
        
        self.label = ttk.Label(self, text="Preparando...")
        self.label.pack(pady=10)
        
        self.progress = ttk.Progressbar(self, variable=self.var, maximum=max_value, length=350)
        self.progress.pack(pady=5)
        
        self.status_label = ttk.Label(self, text="")
        self.status_label.pack(pady=5)
        
        self.cancelled = False
        self.button = ttk.Button(self, text="Cancelar", command=self.cancel)
        self.button.pack(pady=5)
        
        self.center()

    def center(self):
        self.update_idletasks()
        x = (self.winfo_screenwidth() // 2) - (self.winfo_width() // 2)
        y = (self.winfo_screenheight() // 2) - (self.winfo_height() // 2)
        self.geometry(f"+{x}+{y}")

    def cancel(self):
        self.cancelled = True
        self.destroy()

    def update_progress(self, value, text=None, status=None):
        if self.cancelled:
            return
        self.var.set(min(value, self.max_value))
        if text:
            self.label.config(text=text)
        if status:
            self.status_label.config(text=status)
        self.update_idletasks()


# ------------------------------------------------------------------------------
# RCON
# ------------------------------------------------------------------------------

class RCONError(Exception):
    pass


class RCONClient:
    TYPE_AUTH = 3
    TYPE_EXEC = 2
    TYPE_RESP = 0

    def __init__(self, host="127.0.0.1", port=25575, password="minecraft", timeout=5.0):
        self.host = host
        self.port = int(port)
        self.password = password
        self.timeout = timeout
        self.sock = None
        self.req_id = 0

    def _pack(self, req_id: int, req_type: int, body: str) -> bytes:
        payload = struct.pack("<ii", req_id, req_type) + body.encode("utf-8") + b"\x00\x00"
        length = struct.pack("<i", len(payload))
        return length + payload

    def _read_packet(self) -> tuple:
        def recvall(n):
            data = b""
            while len(data) < n:
                part = self.sock.recv(n - len(data))
                if not part:
                    raise RCONError("Conexión RCON cerrada")
                data += part
            return data

        raw_len = recvall(4)
        (length,) = struct.unpack("<i", raw_len)
        payload = recvall(length)
        req_id, resp_type = struct.unpack("<ii", payload[:8])
        body = payload[8:-2].decode("utf-8", errors="replace")
        return req_id, resp_type, body

    def connect(self):
        self.sock = socket.create_connection((self.host, self.port), timeout=self.timeout)
        self.sock.settimeout(self.timeout)
        # Auth
        self.req_id += 1
        self.sock.sendall(self._pack(self.req_id, self.TYPE_AUTH, self.password))
        rid, rtype, body = self._read_packet()
        if rid == -1:
            raise RCONError("Auth RCON fallida (password incorrecto)")

    def command(self, cmd: str) -> str:
        if self.sock is None:
            self.connect()
        self.req_id += 1
        self.sock.sendall(self._pack(self.req_id, self.TYPE_EXEC, cmd))
        rid, rtype, body = self._read_packet()
        return body

    def close(self):
        try:
            if self.sock:
                self.sock.close()
        finally:
            self.sock = None


# ------------------------------------------------------------------------------
# Descarga de versiones (Mojang) y Forge
# ------------------------------------------------------------------------------

def fetch_manifest():
    last_err = None
    for url in MOJANG_MANIFEST_URLS:
        try:
            r = requests.get(url, timeout=30)
            if r.ok:
                return r.json()
        except Exception as e:
            last_err = e
    raise RuntimeError(f"No se pudo obtener el manifest de versiones. Último error: {last_err}")


def pick_version(manifest: dict, preference: str) -> dict:
    if not manifest:
        raise ValueError("Manifest vacío")
    latest = manifest.get("latest", {}) or {}
    versions = manifest.get("versions", []) or []
    if preference == "latest-release":
        target_id = latest.get("release")
    elif preference == "latest-snapshot":
        target_id = latest.get("snapshot")
    else:
        target_id = preference
    if not target_id:
        raise RuntimeError("No se pudo resolver la versión preferida.")
    for v in versions:
        if v.get("id") == target_id:
            return v
    for v in versions:
        if v.get("type") == "release":
            return v
    if versions:
        return versions[0]
    raise RuntimeError("No hay versiones disponibles en el manifest.")


def fetch_version_detail(url: str) -> dict:
    r = requests.get(url, timeout=30)
    r.raise_for_status()
    return r.json()


def download_with_progress(session: requests.Session, url: str, dest_path: str, progress_cb=None):
    with session.get(url, stream=True, timeout=60) as r:
        r.raise_for_status()
        total = int(r.headers.get("Content-Length", 0))
        downloaded = 0
        chunk = 1024 * 128
        with open(dest_path, "wb") as f:
            for part in r.iter_content(chunk_size=chunk):
                if part:
                    f.write(part)
                    downloaded += len(part)
                    if progress_cb:
                        progress_cb(downloaded, total)


def download_forge_installer(mc_version: str, forge_version: str, dest_dir: str, progress_cb=None):
    if not forge_version:
        raise RuntimeError("Versión de Forge vacía.")
    # Strip (recommended) or (latest) if present
    forge_num = forge_version.split(' (')[0]
    full = f"{mc_version}-{forge_num}" if not forge_num.startswith(f"{mc_version}-") else forge_num
    dest_path = os.path.join(dest_dir, f"forge-{full}-installer.jar")
    urls = [
        f"https://maven.minecraftforge.net/net/minecraftforge/forge/{full}/forge-{full}-installer.jar",
        f"https://files.minecraftforge.net/maven/net/minecraftforge/forge/{full}/forge-{full}-installer.jar",
    ]
    sess = requests.Session()
    last_error = None
    for u in urls:
        try:
            download_with_progress(sess, u, dest_path, progress_cb)
            return dest_path
        except Exception as e:
            last_error = e
    raise RuntimeError(f"No se pudo descargar Forge ({full}): {last_error}")


def install_forge_server(installer_path: str, server_dir: str, java_path: str):
    args = [java_path, "-jar", installer_path, "--installServer"]
    try:
        result = subprocess.run(args, capture_output=True, text=True, timeout=1200, cwd=server_dir)
        if result.returncode != 0:
            err = result.stderr or result.stdout or "Error desconocido"
            raise RuntimeError(f"Error instalando Forge: {err}")
        # Alias server.jar -> jar de Forge encontrado
        forge_jar = None
        candidates = sorted(Path(server_dir).glob("forge-*.jar")) + \
                     sorted(Path(server_dir).glob("forge-*universal*.jar")) + \
                     [p for p in Path(server_dir).glob("*.jar") if "forge" in p.name.lower()]
        if candidates:
            forge_jar = candidates[0]
        if not forge_jar:
            raise RuntimeError("No se encontró el jar de Forge tras la instalación.")
        alias = Path(server_dir) / SERVER_JAR_ALIAS
        if alias.exists():
            alias.unlink()
        if is_windows():
            shutil.copyfile(forge_jar, alias)
        else:
            os.symlink(forge_jar.name, alias)
    except subprocess.TimeoutExpired:
        raise RuntimeError("Timeout instalando Forge (20+ min)")
    except Exception as e:
        raise RuntimeError(f"Instalador Forge falló: {e}")


# ------------------------------------------------------------------------------
# Gestión de procesos (STDIN/OUT + PTY opcional en Unix)
# ------------------------------------------------------------------------------

class ProcessReader(threading.Thread):
    """Lector de líneas para un stream o fd (modo texto)."""

    def __init__(self, stream, q: queue.Queue, tag: str, color_hint=None):
        super().__init__(daemon=True)
        self.stream = stream
        self.q = q
        self.tag = tag
        self.color_hint = color_hint

    def run(self):
        try:
            for line in iter(self.stream.readline, ''):
                if not line:
                    break
                self.q.put((self.tag, line.rstrip("\r\n"), self.color_hint))
        except Exception as e:
            self.q.put((self.tag, f"[Lector error] {e}", self.color_hint))
        finally:
            try:
                self.stream.close()
            except Exception:
                pass


class ManagedProcess:
    """Envuelve Popen. En Unix puede usar PTY para evitar JLine."""

    def __init__(self, name: str, q: queue.Queue):
        self.name = name
        self.q = q
        self.proc = None
        self.stdout_reader = None
        self.stderr_reader = None
        self._pty_master = None  # solo Unix
        self._pty_reader_file = None

    def is_running(self) -> bool:
        return self.proc is not None and self.proc.poll() is None

    def start(self, args, cwd=None, env=None, stdin_pipe=True, use_pty=False):
        if self.is_running():
            return

        self.q.put(("sys", f"[{self.name}] Lanzando: {' '.join(args)}", None))

        creationflags = 0
        preexec_fn = None
        start_new_session = False
        if is_windows():
            creationflags = subprocess.CREATE_NEW_PROCESS_GROUP
        else:
            start_new_session = True  # nueva sesión -> podremos killpg

        try:
            if use_pty and not is_windows():
                import pty, os as _os, io
                m, s = pty.openpty()
                self._pty_master = m
                # Usamos el slave como stdin/stdout/stderr del proceso
                self.proc = subprocess.Popen(
                    args,
                    cwd=cwd,
                    env=env,
                    stdin=s,
                    stdout=s,
                    stderr=s,
                    text=True,
                    bufsize=1,
                    universal_newlines=True,
                    start_new_session=start_new_session
                )
                # Cerramos el slave en el padre; leemos el master como archivo de texto
                _os.close(s)
                self._pty_reader_file = io.open(m, mode="r", buffering=1, encoding="utf-8", errors="replace")
                self.stdout_reader = ProcessReader(self._pty_reader_file, self.q, self.name, None)
                self.stdout_reader.start()
                self.stderr_reader = None
            else:
                self.proc = subprocess.Popen(
                    args,
                    cwd=cwd,
                    env=env,
                    stdin=subprocess.PIPE if stdin_pipe else None,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    bufsize=1,
                    universal_newlines=True,
                    creationflags=creationflags,
                    start_new_session=start_new_session
                )
                self.stdout_reader = ProcessReader(self.proc.stdout, self.q, self.name, None)
                self.stderr_reader = ProcessReader(self.proc.stderr, self.q, self.name, None)
                self.stdout_reader.start()
                self.stderr_reader.start()
        except Exception as e:
            self.q.put(("sys", f"[{self.name}] Error al iniciar: {e}", None))
            raise

    def sendline(self, text: str):
        if not self.is_running():
            return False
        try:
            if self.proc.stdin and self.proc.stdin.writable():
                self.proc.stdin.write(text + "\n")
                self.proc.stdin.flush()
                return True
            else:
                # Si estamos en PTY, escribir al master
                if self._pty_master is not None:
                    import os as _os
                    _os.write(self._pty_master, (text + "\n").encode("utf-8", errors="ignore"))
                    return True
        except Exception as e:
            self.q.put(("sys", f"[{self.name}] Error al enviar comando: {e}", None))
        return False

    def terminate(self, gently=False, gentle_cmd=None, wait_sec=12):
        if not self.is_running():
            return
        try:
            if gently:
                # Guardado explícito antes de parar
                self.q.put(("sys", f"[{self.name}] Guardando mundo...", None))
                self.sendline("save-all flush")
                time.sleep(0.6)
                if gentle_cmd:
                    self.q.put(("sys", f"[{self.name}] Deteniendo con '{gentle_cmd}'...", None))
                    self.sendline(gentle_cmd)
                deadline = time.time() + wait_sec
                while self.is_running() and time.time() < deadline:
                    time.sleep(0.2)

            if self.is_running():
                self.q.put(("sys", f"[{self.name}] Terminando proceso...", None))
                if is_windows():
                    # Mata el árbol de procesos
                    try:
                        subprocess.run(["taskkill", "/PID", str(self.proc.pid), "/T", "/F"],
                                       capture_output=True, text=True, timeout=5)
                    except Exception:
                        self.proc.terminate()
                else:
                    import os as _os
                    try:
                        pgid = _os.getpgid(self.proc.pid)
                        _os.killpg(pgid, signal.SIGTERM)
                    except Exception:
                        self.proc.terminate()

            deadline = time.time() + 5
            while self.is_running() and time.time() < deadline:
                time.sleep(0.2)

            if self.is_running():
                self.q.put(("sys", f"[{self.name}] Forzando cierre...", None))
                if is_windows():
                    self.proc.kill()
                else:
                    import os as _os
                    try:
                        pgid = _os.getpgid(self.proc.pid)
                        _os.killpg(pgid, signal.SIGKILL)
                    except Exception:
                        self.proc.kill()
        except Exception as e:
            self.q.put(("sys", f"[{self.name}] Error al terminar: {e}", None))
        finally:
            # Cierra PTY y lectores
            try:
                if self.stdout_reader and self.stdout_reader.is_alive():
                    # no hay join duro; dejamos que cierre solo
                    pass
                if self.stderr_reader and self.stderr_reader.is_alive():
                    pass
                if self._pty_reader_file:
                    self._pty_reader_file.close()
            except Exception:
                pass
            self.proc = None
            self._pty_master = None
            self._pty_reader_file = None


# ------------------------------------------------------------------------------
# GUI
# ------------------------------------------------------------------------------

class ScrollableFrame(ttk.Frame):
    """Un frame con scrollbar vertical usando Canvas."""
    def __init__(self, parent, **kwargs):
        super().__init__(parent, **kwargs)
        self.canvas = tk.Canvas(self, highlightthickness=0)
        self.scrollbar = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.inner = ttk.Frame(self.canvas)

        self.inner.bind(
            "<Configure>",
            lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        )
        self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.canvas.configure(yscrollcommand=self.scrollbar.set)

        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.scrollbar.grid(row=0, column=1, sticky="ns")

        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=1)

        # Soporte rueda del mouse
        self.canvas.bind_all("<MouseWheel>", self._on_mousewheel)      # Windows/macOS
        self.canvas.bind_all("<Button-4>", self._on_mousewheel_linux)  # Linux up
        self.canvas.bind_all("<Button-5>", self._on_mousewheel_linux)  # Linux down

    def _on_mousewheel(self, event):
        # Verifica que el Canvas aún exista antes de intentar desplazarlo
        if self.canvas.winfo_exists():
            # Windows/macOS
            self.canvas.yview_scroll(int(-1*(event.delta/120)), "units")

    def _on_mousewheel_linux(self, event):
        if self.canvas.winfo_exists():
            if event.num == 4:
                self.canvas.yview_scroll(-3, "units")
            elif event.num == 5:
                self.canvas.yview_scroll(3, "units")


class MinecraftGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_NAME)
        
        # Cargar configuración antes de establecer geometría
        self._load_app_config()
        
        # Establecer geometría guardada o por defecto
        geometry = self.app_config.get("window_geometry", "1120x760")
        self.geometry(geometry)
        self.minsize(980, 640)

        # Configurar logging
        self._setup_logging()

        # Estilo
        self._init_style()

        # Estado
        self.server_properties = DEFAULT_SERVER_PROPERTIES.copy()
        self.players_online = set()
        self.public_address = ""
        self._public_candidates = []
        self.manifest_cache = None
        self.console_queue = queue.Queue()
        self._ready_seen_once = False
        self._autosave_thread = None
        self._autosave_stop = threading.Event()
        self._rcon_lock = threading.Lock()

        self.server_proc = ManagedProcess("MC", self.console_queue)
        self.playit_proc = ManagedProcess("playit", self.console_queue)

        # UI
        self._build_ui()
        self._load_server_properties()
        self._refresh_status_labels()

        self.protocol("WM_DELETE_WINDOW", self._on_exit)
        self.after(80, self._drain_console_queue)

    # ---------- Logging ----------

    def _setup_logging(self):
        """Configura el sistema de logging con rotación de archivos."""
        log_dir = APP_STATE_DIR / "logs"
        ensure_dir(str(log_dir))
        log_file = log_dir / "app.log"
        
        self.logger = logging.getLogger(APP_NAME)
        self.logger.setLevel(logging.INFO)
        
        # Evitar múltiples handlers si se reinicia la app
        if not self.logger.handlers:
            handler = RotatingFileHandler(
                log_file, 
                maxBytes=2*1024*1024,  # 2 MB
                backupCount=3,
                encoding='utf-8'
            )
            formatter = logging.Formatter(
                '%(asctime)s - %(levelname)s - %(message)s',
                datefmt='%Y-%m-%d %H:%M:%S'
            )
            handler.setFormatter(formatter)
            self.logger.addHandler(handler)

    # ---------- Estilo ----------

    def _init_style(self):
        style = ttk.Style()
        # Selecciona un tema fiable
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("TButton", padding=6)
        style.configure("Header.TLabel", font=("Segoe UI", 11, "bold"))
        style.configure("Status.TLabel", font=("Segoe UI", 10))
        style.configure("Pill.Green.TLabel", background="#2e7d32", foreground="white", padding=(8,2))
        style.configure("Pill.Red.TLabel", background="#b71c1c", foreground="white", padding=(8,2))
        style.configure("Pill.Gray.TLabel", background="#424242", foreground="white", padding=(8,2))

    # ---------- UI principal ----------

    def _build_ui(self):
        # Menú
        menubar = tk.Menu(self)
        
        # Menú Archivo
        filemenu = tk.Menu(menubar, tearoff=False)
        filemenu.add_command(label="Abrir carpeta del servidor", command=self._open_server_dir)
        filemenu.add_command(label="Abrir carpeta de mods", command=self._open_mods_dir)
        filemenu.add_separator()
        filemenu.add_command(label="Crear backup del mundo", command=self._create_backup)
        filemenu.add_command(label="Restaurar backup", command=self._restore_backup)
        filemenu.add_separator()
        filemenu.add_command(label="Importar jar de Forge", command=self._import_forge_jar)
        filemenu.add_separator()
        filemenu.add_command(label="Salir", command=self._on_exit)
        menubar.add_cascade(label="Archivo", menu=filemenu)

        # Menú Ver
        viewmenu = tk.Menu(menubar, tearoff=False)
        viewmenu.add_command(label="Limpiar consola", command=lambda: self.console.delete("1.0", tk.END))
        viewmenu.add_checkbutton(label="Autoscroll", variable=tk.BooleanVar(value=self.app_config.get("console_autoscroll", True)), command=self._toggle_autoscroll)
        viewmenu.add_checkbutton(label="Ocultar logs INFO", variable=tk.BooleanVar(value=self.app_config.get("hide_info_logs", False)), command=self._toggle_hide_info)
        menubar.add_cascade(label="Ver", menu=viewmenu)

        # Menú Ayuda
        helpmenu = tk.Menu(menubar, tearoff=False)
        helpmenu.add_command(label="Ayuda rápida", command=self._show_help)
        helpmenu.add_command(label="Acerca de", command=self._show_about)
        menubar.add_cascade(label="Ayuda", menu=helpmenu)
        self.config(menu=menubar)

        # Toolbar
        toolbar = ttk.Frame(self, padding=(10, 8))
        toolbar.pack(side=tk.TOP, fill=tk.X)

        self.btn_create = ttk.Button(toolbar, text="Crear Servidor", command=self._on_create_server)
        self.btn_start = ttk.Button(toolbar, text="Iniciar Servidor", command=self._on_start_server)
        self.btn_stop = ttk.Button(toolbar, text="Detener Servidor", command=self._on_stop_server)
        self.btn_playit = ttk.Button(toolbar, text="Iniciar playit.gg", command=self._on_start_playit)
        self.btn_config = ttk.Button(toolbar, text="Configurar", command=self._open_config_dialog)

        self.btn_create.pack(side=tk.LEFT, padx=4)
        self.btn_start.pack(side=tk.LEFT, padx=4)
        self.btn_stop.pack(side=tk.LEFT, padx=4)
        self.btn_playit.pack(side=tk.LEFT, padx=16)
        self.btn_config.pack(side=tk.LEFT, padx=4)

        # Consola
        console_frame = ttk.Frame(self, padding=(10, 6))
        console_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        # Panel izquierdo: consola
        left = ttk.Frame(console_frame)
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.console = tk.Text(left, wrap="none", height=24, font=("Consolas", 10))
        
        # Menú contextual para la consola
        self.console_menu = tk.Menu(self.console, tearoff=0)
        self.console_menu.add_command(label="Copiar", command=self._copy_console_selection)
        self.console_menu.add_command(label="Seleccionar todo", command=self._select_all_console)
        self.console_menu.add_separator()
        self.console_menu.add_command(label="Limpiar", command=lambda: self.console.delete("1.0", tk.END))
        
        self.console.bind("<Button-3>", self._show_console_menu)  # Click derecho

        ysb = ttk.Scrollbar(left, orient="vertical", command=self.console.yview)
        xsb = ttk.Scrollbar(left, orient="horizontal", command=self.console.xview)
        self.console.configure(yscrollcommand=ysb.set, xscrollcommand=xsb.set)

        self.console.grid(row=0, column=0, sticky="nsew")
        ysb.grid(row=0, column=1, sticky="ns")
        xsb.grid(row=1, column=0, sticky="ew")
        left.rowconfigure(0, weight=1)
        left.columnconfigure(0, weight=1)

        # Tags de color en consola
        self.console.tag_configure("INFO", foreground="#1e88e5")
        self.console.tag_configure("WARN", foreground="#b28704")
        self.console.tag_configure("ERROR", foreground="#c62828")
        self.console.tag_configure("CHAT", foreground="#2e7d32")
        self.console.tag_configure("SYS", foreground="#6d4c41")

        # Panel derecho: estado
        right = ttk.Frame(console_frame, padding=(8, 6))
        right.pack(side=tk.LEFT, fill=tk.Y)

        ttk.Label(right, text="Estado", style="Header.TLabel").pack(anchor="w", pady=(0,6))
        self.lbl_state_server = ttk.Label(right, text="Servidor: detenido", style="Status.TLabel")
        self.lbl_state_server.pack(anchor="w", pady=2)
        self.lbl_state_players = ttk.Label(right, text="Jugadores: 0", style="Status.TLabel")
        self.lbl_state_players.pack(anchor="w", pady=2)
        self.lbl_state_local = ttk.Label(right, text=f"Local: {local_ip()}:{DEFAULT_APP_CONFIG['server_port']}", style="Status.TLabel")
        self.lbl_state_local.pack(anchor="w", pady=2)
        self.lbl_state_public = ttk.Label(right, text="Pública: (playit.gg no iniciado)", style="Status.TLabel")
        self.lbl_state_public.pack(anchor="w", pady=2)

        ttk.Separator(right, orient="horizontal").pack(fill=tk.X, pady=8)
        ttk.Label(right, text="Dirección pública", style="Header.TLabel").pack(anchor="w", pady=(0,6))
        self.var_public = tk.StringVar(value="(sin detectar)")
        self.cb_public = ttk.Combobox(right, textvariable=self.var_public, state="readonly", width=34)
        self.cb_public.pack(anchor="w", pady=2)
        
        public_buttons = ttk.Frame(right)
        public_buttons.pack(anchor="w", pady=2)
        ttk.Button(public_buttons, text="Copiar", command=self._copy_public).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(public_buttons, text="Abrir", command=self._open_public).pack(side=tk.LEFT)

        ttk.Separator(right, orient="horizontal").pack(fill=tk.X, pady=8)
        ttk.Label(right, text="RCON", style="Header.TLabel").pack(anchor="w", pady=(0,6))
        self.lbl_rcon = ttk.Label(right, text="Estado: desconocido", style="Status.TLabel")
        self.lbl_rcon.pack(anchor="w", pady=2)
        ttk.Button(right, text="Probar RCON", command=self._test_rcon).pack(anchor="w", pady=2)

        # Línea de comandos
        cmd_frame = ttk.Frame(self, padding=(10, 6))
        cmd_frame.pack(side=tk.TOP, fill=tk.X)
        ttk.Label(cmd_frame, text="Comando (MC/RCON):").pack(side=tk.LEFT)
        self.entry_cmd = ttk.Entry(cmd_frame)
        self.entry_cmd.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=6)
        ttk.Button(cmd_frame, text="Enviar", command=self._send_server_cmd).pack(side=tk.LEFT)
        self.entry_cmd.bind("<Return>", lambda e: self._send_server_cmd())

        # Barra inferior
        bottom = ttk.Frame(self, padding=(10, 6))
        bottom.pack(side=tk.BOTTOM, fill=tk.X)
        
        self.var_autoscroll = tk.BooleanVar(value=self.app_config.get("console_autoscroll", True))
        ttk.Checkbutton(bottom, text="Autoscroll", variable=self.var_autoscroll,
                        command=self._toggle_autoscroll).pack(side=tk.RIGHT)
        
        self.var_hide_info = tk.BooleanVar(value=self.app_config.get("hide_info_logs", False))
        ttk.Checkbutton(bottom, text="Ocultar INFO", variable=self.var_hide_info,
                        command=self._toggle_hide_info).pack(side=tk.RIGHT, padx=(0, 10))
        
        ttk.Button(bottom, text="Salir", command=self._on_exit).pack(side=tk.RIGHT, padx=6)

    # ---------- Menú contextual consola ----------

    def _show_console_menu(self, event):
        """Muestra el menú contextual en la consola."""
        try:
            self.console_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.console_menu.grab_release()

    def _copy_console_selection(self):
        """Copia la selección actual de la consola al portapapeles."""
        try:
            selected = self.console.get(tk.SEL_FIRST, tk.SEL_LAST)
            self.clipboard_clear()
            self.clipboard_append(selected)
        except tk.TclError:
            # No hay selección
            pass

    def _select_all_console(self):
        """Selecciona todo el texto de la consola."""
        self.console.tag_add(tk.SEL, "1.0", tk.END)
        self.console.mark_set(tk.INSERT, "1.0")
        self.console.see(tk.INSERT)

    # ---------- Cargar/Guardar ----------

    @property
    def server_dir(self) -> str:
        return self.app_config.get("server_dir", DEFAULT_SERVER_DIR)

    @property
    def server_jar_alias_path(self) -> str:
        return str(Path(self.server_dir) / SERVER_JAR_ALIAS)

    @property
    def mods_dir(self) -> str:
        return str(Path(self.server_dir) / "mods")

    def _app_config_path(self) -> str:
        return str(APP_STATE_DIR / APP_CONFIG_NAME)

    def _server_properties_path(self) -> str:
        return str(Path(self.server_dir) / "server.properties")

    def _eula_path(self) -> str:
        return str(Path(self.server_dir) / "eula.txt")

    def _server_exists(self) -> bool:
        return Path(self.server_jar_alias_path).exists() and Path(self._eula_path()).exists()

    def _load_app_config(self):
        # Inicializar con valores por defecto
        self.app_config = DEFAULT_APP_CONFIG.copy()
        
        try:
            ensure_dir(str(APP_STATE_DIR))
            p = Path(self._app_config_path())
            if p.exists():
                with open(p, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    self.app_config.update(data or {})
        except Exception as e:
            print(f"Error cargando app_config: {e}")
        ensure_dir(self.server_dir)

    def _save_app_config(self):
        try:
            ensure_dir(str(APP_STATE_DIR))
            with open(self._app_config_path(), "w", encoding="utf-8") as f:
                json.dump(self.app_config, f, indent=2, ensure_ascii=False)
        except Exception as e:
            self._log_sys(f"Error guardando app_config: {e}")

    def _load_server_properties(self):
        try:
            p = Path(self._server_properties_path())
            if p.exists():
                props_txt = read_text_file(str(p))
                props = parse_properties(props_txt)
                self.server_properties = merge_properties(props, DEFAULT_SERVER_PROPERTIES)
            else:
                self.server_properties = DEFAULT_SERVER_PROPERTIES.copy()
        except Exception as e:
            self._log_sys(f"Error cargando server.properties: {e}")

    def _save_server_properties(self):
        try:
            if self.app_config.get("enable_rcon", True):
                self.server_properties["enable-rcon"] = "true"
                self.server_properties["rcon.port"] = str(self.app_config.get("rcon_port", 25575))
                self.server_properties["rcon.password"] = self.app_config.get("rcon_password", "minecraft")

            if self.app_config.get("enable_opt_properties", True):
                self.server_properties.setdefault("sync-chunk-writes", "false")
                self.server_properties.setdefault("network-compression-threshold", "512")
                self.server_properties.setdefault("max-tick-time", "60000")

            # Escritura en latin-1 (seguro para MOTD y compañía)
            write_properties_file(self._server_properties_path(), self.server_properties)
        except Exception as e:
            self._log_sys(f"Error guardando server.properties: {e}")

    # ---------- Consola ----------

    def _toggle_autoscroll(self):
        self.app_config["console_autoscroll"] = bool(self.var_autoscroll.get())
        self._save_app_config()

    def _toggle_hide_info(self):
        self.app_config["hide_info_logs"] = bool(self.var_hide_info.get())
        self._save_app_config()

    def _console_insert(self, tag: str, text: str):
        # Si está activado ocultar INFO y es un log INFO, no mostrar
        if (self.var_hide_info.get() and tag == "MC" and 
            "INFO" in text and not any(x in text for x in ["CHAT", "WARN", "ERROR"])):
            return
            
        # Detectar nivel/CHAT y aplicar tag
        tag_use = None
        if tag == "sys":
            tag_use = "SYS"
        else:
            msg = text
            if "ERROR" in msg or "[ERROR]" in msg:
                tag_use = "ERROR"
            elif "WARN" in msg or "[WARN]" in msg or "[Warning]" in msg:
                tag_use = "WARN"
            else:
                # Chat ej: [Server thread/INFO]: <User> hola
                if RE_CHAT.search(msg):
                    tag_use = "CHAT"
                else:
                    tag_use = "INFO"

        # Escribir en el logger
        self.logger.info(f"[{tag}] {text}")
        
        # Insertar en la consola gráfica
        self.console.insert(tk.END, f"[{timestamp()}] {text}\n", tag_use)
        if self.var_autoscroll.get():
            self.console.see(tk.END)

    def _log_sys(self, text: str):
        self._console_insert("sys", text)

    def _drain_console_queue(self):
        try:
            while True:
                tag, line, _ = self.console_queue.get_nowait()
                if tag == "MC":
                    self._handle_mc_log_line(line)
                    self._console_insert(tag, f"{line}")
                elif tag == "playit":
                    self._handle_playit_log_line(line)
                    if not self.app_config.get("hide_playit_logs", True):
                        self._console_insert(tag, f"{line}")
                else:
                    self._console_insert(tag, f"{line}")
        except queue.Empty:
            pass
        self.after(80, self._drain_console_queue)

    def _handle_mc_log_line(self, line: str):
        if m := RE_JOIN.search(line):
            self.players_online.add(m.group(1))
            self._refresh_status_labels()
        if m := RE_LEAVE.search(line):
            self.players_online.discard(m.group(1))
            self._refresh_status_labels()
        for hint in READY_HINTS:
            if hint in line:
                self._ready_seen_once = True
                if self.app_config.get("auto_start_playit", True) and not self.playit_proc.is_running():
                    self._on_start_playit()
                break

    def _handle_playit_log_line(self, line: str):
        host_port = None
        if m := RE_PUBLIC_HOST.search(line):
            host = m.group(1)
            port = m.group(2) or ""
            host_port = f"{host}:{port}" if port else host
        else:
            if m2 := RE_GENERIC_TCP.search(line):
                if not re.match(r"^\d{1,3}(\.\d{1,3}){3}$", m2.group(2)):
                    host_port = f"{m2.group(2)}:{m2.group(3)}"
        if host_port and host_port not in self._public_candidates:
            self._public_candidates.append(host_port)
            # Ordenar: joinmc.link primero
            self._public_candidates.sort(key=lambda hp: (".joinmc.link" not in hp, ".playit.gg" not in hp, hp))
            self.cb_public["values"] = self._public_candidates
            saved = self.app_config.get("tunnels_per_dir", {}).get(self.server_dir, "")
            choice = saved if saved in self._public_candidates else (self._public_candidates[0] if self._public_candidates else "")
            self.var_public.set(choice)
            self.public_address = choice
            tunnels = self.app_config.get("tunnels_per_dir", {})
            tunnels[self.server_dir] = choice
            self.app_config["tunnels_per_dir"] = tunnels
            self.app_config["last_public_address"] = choice
            self._save_app_config()
            self._refresh_status_labels()

    # ---------- Estado / Botones ----------

    def _refresh_status_labels(self):
        s = "corriendo" if self.server_proc.is_running() else "detenido"
        self.lbl_state_server.config(text=f"Servidor: {s}")
        self.lbl_state_players.config(text=f"Jugadores: {len(self.players_online)}")
        port = int(self.app_config.get("server_port", 25565))
        self.lbl_state_local.config(text=f"Local: {local_ip()}:{port}")
        pub = self.public_address or self.app_config.get("tunnels_per_dir", {}).get(self.server_dir, "") \
              or self.app_config.get("last_public_address") or "(playit.gg no iniciado)"
        self.lbl_state_public.config(text=f"Pública: {pub}")

        # RCON indicador
        rcon_ok = self._probe_rcon()
        self.lbl_rcon.config(text=f"RCON: {'OK' if rcon_ok else 'no disponible'}")

        self.btn_create.config(state=("disabled" if self._server_exists() else "normal"))
        self.btn_start.config(state=("disabled" if not self._server_exists() else "normal"))
        self.btn_stop.config(state=("normal" if self.server_proc.is_running() else "disabled"))
        self.btn_playit.config(state=("normal" if self._server_exists() else "disabled"))

    # ---------- Acciones ----------

    def _on_create_server(self):
        try:
            ensure_dir(self.server_dir)
            self._log_sys(f"Carpeta del servidor: {self.server_dir}")
            
            # Generar contraseña RCON aleatoria si es la default
            if self.app_config.get("rcon_password", "minecraft") == "minecraft":
                new_pass = generate_random_password()
                self.app_config["rcon_password"] = new_pass
                self._save_app_config()
                self._log_sys(f"Contraseña RCON generada automáticamente: {new_pass}")
            
            if self.app_config.get("server_type", "vanilla") == "vanilla":
                self._create_vanilla_server()
            else:
                self._create_forge_server()
        except Exception as e:
            self._log_sys(f"Error al crear servidor: {e}")
            messagebox.showerror("Error", f"No fue posible crear el servidor:\n{e}\n\n{traceback.format_exc()}")

    def _create_vanilla_server(self):
        self._log_sys("Obteniendo manifest de versiones...")
        self.manifest_cache = fetch_manifest()
        pref = self.app_config.get("mc_version", "latest-release")
        vobj = pick_version(self.manifest_cache, pref)
        ver_id = vobj.get("id")
        v_url = vobj.get("url")
        self._log_sys(f"Versión seleccionada: {ver_id}")
        vdetail = fetch_version_detail(v_url)
        server_download = vdetail.get("downloads", {}).get("server", {})
        jar_url = server_download.get("url")
        if not jar_url:
            raise RuntimeError("No se encontró URL del server.jar en el manifest.")
        jar_name = SERVER_JAR_BASENAME.format(version=ver_id)
        jar_path = str(Path(self.server_dir) / jar_name)
        alias_path = self.server_jar_alias_path

        if not Path(jar_path).exists():
            self._log_sys(f"Descargando server.jar ({ver_id})...")
            
            # Diálogo de progreso
            progress_dialog = ProgressDialog(self, title="Descargando server.jar", max_value=100)
            
            def download_thread():
                try:
                    sess = requests.Session()
                    
                    def progress_cb(done, total):
                        percent = 100.0 * done / total if total > 0 else 0
                        status = f"{human_size(done)}/{human_size(total)}" if total > 0 else f"{human_size(done)}"
                        progress_dialog.update_progress(
                            percent, 
                            f"Descargando server.jar...", 
                            status
                        )
                    
                    download_with_progress(sess, jar_url, jar_path, progress_cb=progress_cb)
                    
                    # Cerrar diálogo
                    self.after(0, progress_dialog.destroy)
                    self.after(0, lambda: self._log_sys("Descarga completa."))
                    
                except Exception as e:
                    self.after(0, lambda: progress_dialog.destroy())
                    self.after(0, lambda: self._log_sys(f"Error en descarga: {e}"))
                    raise
            
            # Ejecutar descarga en hilo separado
            threading.Thread(target=download_thread, daemon=True).start()
            
            # Esperar a que termine el diálogo
            self.wait_window(progress_dialog)

        try:
            if Path(alias_path).exists():
                Path(alias_path).unlink()
            shutil.copyfile(jar_path, alias_path)
        except Exception:
            alias_path = jar_path

        write_text_file(self._eula_path(), "eula=true\n")
        self._log_sys("EULA aceptado (eula.txt = true).")

        if not Path(self._server_properties_path()).exists():
            self.server_properties["server-port"] = str(self.app_config.get("server_port", 25565))
            self._save_server_properties()
            self._log_sys("server.properties generado.")

        self._log_sys("Arranque inicial (generar mundo)...")
        self._start_server_impl(initial_boot=True)

    def _create_forge_server(self):
        try:
            self._log_sys("Obteniendo manifest de versiones...")
            self.manifest_cache = fetch_manifest()
            pref = self.app_config.get("mc_version", "latest-release")
            vobj = pick_version(self.manifest_cache, pref)
            ver_id = vobj.get("id")
            self._log_sys(f"Versión de Minecraft: {ver_id}")

            forge_version = self.app_config.get("forge_version", "")
            if not forge_version:
                raise RuntimeError("Selecciona la versión de Forge en Configurar antes de crear.")
            self._log_sys(f"Instalando Forge {forge_version} para {ver_id}...")

            # Diálogo de progreso para Forge
            progress_dialog = ProgressDialog(self, title="Descargando Forge", max_value=100)
            
            def download_forge_thread():
                try:
                    def cb(done, total):
                        percent = 100.0 * done / total if total > 0 else 0
                        status = f"{human_size(done)}/{human_size(total)}" if total > 0 else f"{human_size(done)}"
                        progress_dialog.update_progress(
                            percent,
                            f"Descargando Forge...",
                            status
                        )
                    
                    installer = download_forge_installer(ver_id, forge_version, self.server_dir, progress_cb=cb)
                    
                    # Instalar
                    progress_dialog.update_progress(100, "Instalando Forge...", "Instalando...")
                    java = self.app_config.get("java_path") or "java"
                    install_forge_server(installer, self.server_dir, java)
                    
                    self.after(0, progress_dialog.destroy)
                    self.after(0, lambda: self._complete_forge_setup())
                    
                except Exception as e:
                    self.after(0, lambda: progress_dialog.destroy())
                    self.after(0, lambda: self._log_sys(f"Error instalando Forge: {e}"))
                    raise
            
            threading.Thread(target=download_forge_thread, daemon=True).start()
            self.wait_window(progress_dialog)
            
        except Exception as e:
            self._log_sys(f"Error creando servidor Forge: {e}")
            if Path(self.server_jar_alias_path).exists():
                try: 
                    Path(self.server_jar_alias_path).unlink()
                except Exception: 
                    pass
            raise
    
    def _complete_forge_setup(self):
        """Completa la instalación de Forge después de la descarga."""
        ensure_dir(self.mods_dir)
        self._log_sys("Forge instalado y carpeta mods lista.")

        write_text_file(self._eula_path(), "eula=true\n")
        if not Path(self._server_properties_path()).exists():
            self.server_properties["server-port"] = str(self.app_config.get("server_port", 25565))
            self._save_server_properties()

        self._log_sys("Arranque inicial (Forge puede tardar más)...")
        self._start_server_impl(initial_boot=True)

    def _build_jvm_args(self):
        java = self.app_config.get("java_path") or "java"
        xms = f"-Xms{self.app_config.get('ram_min', '1G')}"
        xmx = f"-Xmx{self.app_config.get('ram_max', '2G')}"
        flags = [
            java, xms, xmx,
            # Evitar problemas de entrada/colores con JLine
            "-Dterminal.jline=false",
            "-Dterminal.ansi=true",
            "-Djline.terminal=jline.UnsupportedTerminal",
            "-Dfile.encoding=UTF-8",
        ]
        if self.app_config.get("enable_jvm_optim", True):
            flags += [
                "-XX:+UseG1GC",
                "-XX:+ParallelRefProcEnabled",
                "-XX:MaxGCPauseMillis=100",
                "-XX:+UnlockExperimentalVMOptions",
                "-XX:+DisableExplicitGC",
                "-XX:+AlwaysPreTouch",
                "-XX:G1NewSizePercent=30",
                "-XX:G1MaxNewSizePercent=40",
                "-XX:G1HeapRegionSize=8M",
                "-XX:G1ReservePercent=20",
                "-XX:InitiatingHeapOccupancyPercent=15",
                "-XX:G1MixedGCCountTarget=4",
                "-XX:SurvivorRatio=32",
                "-XX:+PerfDisableSharedMem",
                "-XX:MaxTenuringThreshold=1",
            ]
        return flags

    def _start_server_impl(self, initial_boot=False):
        java = self.app_config.get("java_path") or "java"

        # Solo preguntar si la verificación falla
        if not self._check_java(java):
            ans = messagebox.askyesno(
                "Java no encontrado",
                "No se pudo confirmar Java. ¿Seleccionar ejecutable manualmente?"
            )
            if ans:
                path = filedialog.askopenfilename(
                    title="Selecciona binario de Java",
                    filetypes=[("Ejecutable", "*")]
                )
                if path:
                    self.app_config["java_path"] = path
                    self._save_app_config()
                else:
                    return  # cancelado por el usuario
            else:
                return  # usuario no quiso buscar Java

        # Sincronizar puerto
        try:
            port = str(self.app_config.get("server_port", 25565))
            if self.server_properties.get("server-port") != port:
                self.server_properties["server-port"] = port
                self._save_server_properties()
        except Exception:
            pass

        args = self._build_jvm_args() + ["-jar", self.server_jar_alias_path, "nogui"]

        # Arranque (PTY opcional en Unix)
        use_pty = (not is_windows()) and bool(self.app_config.get("use_pty_on_unix", True))

        self._ready_seen_once = False
        self.players_online.clear()
        self.server_proc.start(args, cwd=self.server_dir, env=os.environ.copy(), stdin_pipe=True, use_pty=use_pty)
        self._refresh_status_labels()

        self._start_autosave_thread()

        if initial_boot:
            def monitor_and_stop_when_ready():
                start = time.time()
                timeout = 420
                done = False
                while time.time() - start < timeout:
                    time.sleep(1)
                    if not self.server_proc.is_running():
                        break
                    if self._ready_seen_once and not done:
                        time.sleep(10)
                        self.server_proc.terminate(gently=True, gentle_cmd="stop", wait_sec=15)
                        self._stop_autosave_thread()
                        self._log_sys("Arranque inicial completo. Mundo generado.")
                        done = True
                        break
                self._refresh_status_labels()
            threading.Thread(target=monitor_and_stop_when_ready, daemon=True).start()

    def _on_start_server(self):
        try:
            if not self._server_exists():
                messagebox.showwarning("Servidor no encontrado", "Primero usa 'Crear Servidor'.")
                return
                
            # Verificar que existe el JAR
            if not Path(self.server_jar_alias_path).exists():
                messagebox.showerror("Error", f"No se encuentra {SERVER_JAR_ALIAS}. ¿Crear servidor de nuevo?")
                return
                
            # Verificar que el puerto esté libre
            port = int(self.app_config.get("server_port", 25565))
            if not is_port_free(port):
                owner = who_uses_port(port)
                ans = messagebox.askyesno(
                    "Puerto ocupado",
                    f"El puerto {port} está ocupado por:\n{owner}\n\n¿Quieres cambiar el puerto en la configuración?"
                )
                if ans:
                    self._open_config_dialog()
                return
                
            if self.server_proc.is_running():
                messagebox.showinfo("Servidor", "Ya está en ejecución.")
                return
                
            # Advertencia RCON
            if self.app_config.get("enable_rcon", True):
                messagebox.showwarning(
                    "RCON Habilitado",
                    "RCON está habilitado. Por seguridad:\n"
                    "• Nunca expongas el puerto RCON a Internet\n"
                    "• Usa contraseñas seguras\n"
                    "• Considera deshabilitarlo si no lo necesitas",
                    parent=self
                )
                
            self._start_server_impl(initial_boot=False)
        except Exception as e:
            self._log_sys(f"Error al iniciar: {e}")
            messagebox.showerror("Error", f"No fue posible iniciar el servidor:\n{e}")

    def _on_stop_server(self):
        try:
            if not self.server_proc.is_running():
                messagebox.showinfo("Servidor", "No está en ejecución.")
                return
            self.server_proc.terminate(gently=True, gentle_cmd="stop", wait_sec=20)
            self._stop_autosave_thread()
            # Puerto ocupado?
            port = int(self.app_config.get("server_port", 25565))
            if not wait_port_release(port, timeout=12):
                owner = who_uses_port(port)
                self._log_sys(f"Advertencia: el puerto {port} sigue ocupado por: {owner}")
                self._log_sys("Puede quedar en TIME_WAIT unos segundos. Si continúa, reinicia Java o cambia el puerto.")
            self._refresh_status_labels()
        except Exception as e:
            self._log_sys(f"Error al detener: {e}")

    def _on_start_playit(self):
        try:
            if self.playit_proc.is_running():
                messagebox.showinfo("playit.gg", "El agente ya está en ejecución.")
                return
            playit_path = self.app_config.get("playit_path") or ""
            extra_dirs = [self.server_dir]
            if not playit_path:
                for c in ["playit", "playit-agent", "playit.exe", "playit-agent.exe"]:
                    if p := find_executable(c, extra_dirs=extra_dirs):
                        playit_path = p
                        break
            if not playit_path:
                ans = messagebox.askyesno("playit.gg no encontrado",
                                          "No se encontró el agente de playit.\n¿Abrir la página oficial de descarga?")
                if ans:
                    webbrowser.open("https://playit.gg/download")
                path = filedialog.askopenfilename(title="Selecciona el ejecutable de playit.gg")
                if path:
                    playit_path = path
                    self.app_config["playit_path"] = path
                    self._save_app_config()
                else:
                    return
            args = [playit_path]
            self._public_candidates.clear()
            self.cb_public["values"] = []
            self.var_public.set("(sin detectar)")
            self.public_address = ""
            self.playit_proc.start(args, cwd=self.server_dir, env=os.environ.copy(), stdin_pipe=False)
            self._refresh_status_labels()
        except Exception as e:
            self._log_sys(f"Error al iniciar playit: {e}")
            messagebox.showerror("Error", f"No fue posible iniciar playit:\n{e}")

    def _copy_public(self):
        val = self.var_public.get()
        if not val or val.startswith("("):
            messagebox.showinfo("Dirección pública", "Aún no se ha detectado una dirección.")
            return
        self.clipboard_clear()
        self.clipboard_append(val)
        self._log_sys(f"Copiado: {val}")
        tunnels = self.app_config.get("tunnels_per_dir", {})
        tunnels[self.server_dir] = val
        self.app_config["tunnels_per_dir"] = tunnels
        self.public_address = val
        self.app_config["last_public_address"] = val
        self._save_app_config()
        self._refresh_status_labels()

    def _open_public(self):
        """Abre la dirección pública en el navegador."""
        val = self.var_public.get()
        if not val or val.startswith("("):
            messagebox.showinfo("Dirección pública", "Aún no se ha detectado una dirección.")
            return
            
        # Para joinmc.link, abrir el panel web
        if "joinmc.link" in val:
            webbrowser.open(f"http://{val}")
        else:
            # Intentar con minecraft:// (no siempre funciona)
            webbrowser.open(f"minecraft://{val}")
            
        self._log_sys(f"Abriendo: {val}")

    def _send_server_cmd(self):
        cmd = self.entry_cmd.get().strip()
        if not cmd:
            return
        sent = False
        if self.server_proc.is_running():
            sent = self.server_proc.sendline(cmd)
            # Eco en UI
            self._console_insert("MC", f"> {cmd}")
        if not sent and self.app_config.get("enable_rcon", True):
            try:
                with self._rcon_lock:
                    rcon = RCONClient("127.0.0.1",
                                      port=int(self.app_config.get("rcon_port", 25575)),
                                      password=self.app_config.get("rcon_password", "minecraft"),
                                      timeout=3.0)
                    rcon.connect()
                    out = rcon.command(cmd)
                    rcon.close()
                    self._console_insert("MC", f"[RCON] {cmd} -> {out.strip()}")
                    sent = True
            except Exception as e:
                self._log_sys(f"RCON no disponible: {e}")
        if not sent:
            messagebox.showwarning("Servidor no accesible",
                                   "No se pudo enviar el comando.\nInicia el servidor desde la app o habilita RCON en Configurar.")
        self.entry_cmd.delete(0, tk.END)

    # ---------- Backups ----------

    def _create_backup(self):
        """Crea un backup comprimido del mundo."""
        world_dir = Path(self.server_dir) / "world"
        if not world_dir.exists():
            messagebox.showwarning("Backup", "No existe la carpeta 'world'.")
            return
            
        backups_dir = Path(self.server_dir) / "backups"
        ensure_dir(str(backups_dir))
        
        timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
        backup_name = f"world-{timestamp}.zip"
        backup_path = backups_dir / backup_name
        
        try:
            with zipfile.ZipFile(backup_path, 'w', zipfile.ZIP_DEFLATED) as zipf:
                for root, dirs, files in os.walk(world_dir):
                    for file in files:
                        file_path = Path(root) / file
                        # Mantener estructura de directorios relativa
                        arcname = file_path.relative_to(world_dir.parent)
                        zipf.write(file_path, arcname)
                        
            size = backup_path.stat().st_size
            self._log_sys(f"Backup creado: {backup_name} ({human_size(size)})")
            messagebox.showinfo("Backup", f"Backup creado exitosamente:\n{backup_name}\n({human_size(size)})")
            
        except Exception as e:
            self._log_sys(f"Error creando backup: {e}")
            messagebox.showerror("Error", f"No se pudo crear el backup:\n{e}")

    def _restore_backup(self):
        """Restaura un backup del mundo."""
        if self.server_proc.is_running():
            messagebox.showwarning("Servidor activo", "Detén el servidor antes de restaurar un backup.")
            return
            
        backup_path = filedialog.askopenfilename(
            title="Selecciona el archivo de backup",
            filetypes=[("Archivos ZIP", "*.zip"), ("Todos los archivos", "*.*")]
        )
        if not backup_path:
            return
            
        world_dir = Path(self.server_dir) / "world"
        
        # Confirmación
        ans = messagebox.askyesno(
            "Restaurar backup",
            f"¿Restaurar backup?\n\nEsto reemplazará la carpeta 'world' actual.\n\nArchivo: {Path(backup_path).name}",
            icon=messagebox.WARNING
        )
        if not ans:
            return
            
        try:
            # Hacer backup del mundo actual si existe
            if world_dir.exists():
                temp_backup = Path(self.server_dir) / f"world-backup-{int(time.time())}.zip"
                with zipfile.ZipFile(temp_backup, 'w', zipfile.ZIP_DEFLATED) as zipf:
                    for root, dirs, files in os.walk(world_dir):
                        for file in files:
                            file_path = Path(root) / file
                            arcname = file_path.relative_to(world_dir.parent)
                            zipf.write(file_path, arcname)
                self._log_sys(f"Backup del mundo actual guardado como: {temp_backup.name}")
            
            # Eliminar mundo actual
            if world_dir.exists():
                shutil.rmtree(world_dir)
                
            # Extraer backup
            with zipfile.ZipFile(backup_path, 'r') as zipf:
                zipf.extractall(self.server_dir)
                
            self._log_sys("Backup restaurado exitosamente.")
            messagebox.showinfo("Backup", "Backup restaurado exitosamente.")
            
        except Exception as e:
            self._log_sys(f"Error restaurando backup: {e}")
            messagebox.showerror("Error", f"No se pudo restaurar el backup:\n{e}")

    # ---------- Auxiliares ----------

    def _start_autosave_thread(self):
        if not self.app_config.get("enable_autosave", True):
            return
        self._autosave_stop.clear()
        if self._autosave_thread and self._autosave_thread.is_alive():
            return
        def run():
            minutes = max(2, int(self.app_config.get("autosave_minutes", 10)))
            while not self._autosave_stop.is_set():
                time.sleep(minutes * 60)
                if self.server_proc.is_running():
                    try:
                        self.server_proc.sendline("save-all flush")
                        self._log_sys("Autosave ejecutado.")
                    except Exception:
                        pass
        self._autosave_thread = threading.Thread(target=run, daemon=True)
        self._autosave_thread.start()

    def _stop_autosave_thread(self):
        self._autosave_stop.set()

    def _check_java(self, java_cmd: str) -> bool:
        try:
            proc = subprocess.run([java_cmd, "-version"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=10)
            out = (proc.stdout or "") + (proc.stderr or "")
            if "version" in out.lower() or "openjdk" in out.lower() or "java" in out.lower():
                self._log_sys(f"Java: {out.splitlines()[0] if out else 'OK'}")
                return True
        except Exception as e:
            self._log_sys(f"No se pudo ejecutar Java: {e}")
        return False

    def _open_server_dir(self):
        try:
            path = self.server_dir
            ensure_dir(path)
            if is_windows():
                os.startfile(path)  # type: ignore
            elif sys.platform == "darwin":
                subprocess.run(["open", path])
            else:
                subprocess.run(["xdg-open", path])
        except Exception as e:
            self._log_sys(f"No se pudo abrir la carpeta: {e}")

    def _open_mods_dir(self):
        try:
            path = self.mods_dir
            ensure_dir(path)
            if is_windows():
                os.startfile(path)  # type: ignore
            elif sys.platform == "darwin":
                subprocess.run(["open", path])
            else:
                subprocess.run(["xdg-open", path])
        except Exception as e:
            self._log_sys(f"No se pudo abrir la carpeta de mods: {e}")

    def _import_forge_jar(self):
        if not self._server_exists():
            messagebox.showwarning("Servidor no creado", "Primero debes crear un servidor.")
            return
        jar_path = filedialog.askopenfilename(title="Selecciona el jar de Forge",
                                              filetypes=[("JAR files", "*.jar"), ("All files", "*.*")])
        if jar_path:
            alias = self.server_jar_alias_path
            if Path(alias).exists():
                Path(alias).unlink()
            shutil.copyfile(jar_path, alias)
            self._log_sys(f"Forge importado: {Path(jar_path).name}")
            messagebox.showinfo("Éxito", f"Jar de Forge importado: {Path(jar_path).name}")

    def _probe_rcon(self) -> bool:
        if not self.app_config.get("enable_rcon", True):
            return False
        try:
            rcon = RCONClient("127.0.0.1",
                              port=int(self.app_config.get("rcon_port", 25575)),
                              password=self.app_config.get("rcon_password", "minecraft"),
                              timeout=0.6)
            rcon.connect()
            rcon.close()
            return True
        except Exception:
            return False

    def _test_rcon(self):
        ok = self._probe_rcon()
        if ok:
            messagebox.showinfo("RCON", "Conexión RCON OK.")
        else:
            messagebox.showwarning("RCON", "No disponible. Asegúrate de:\n"
                                  "1) Habilitar RCON en 'Configurar'.\n"
                                  "2) Reiniciar el servidor para aplicar cambios.\n"
                                  "3) El puerto/contraseña coinciden.")

    def _on_exit(self):
        # Guardar geometría de ventana
        self.app_config["window_geometry"] = self.geometry()
        self._save_app_config()
        
        try:
            if self.server_proc.is_running():
                self.server_proc.terminate(gently=True, gentle_cmd="stop", wait_sec=15)
        except Exception:
            pass
        try:
            if self.playit_proc.is_running():
                self.playit_proc.terminate(gently=False)
        except Exception:
            pass
        self._stop_autosave_thread()
        # pequeña espera opcional para liberar puerto
        try:
            wait_port_release(int(self.app_config.get("server_port", 25565)), timeout=5)
        except Exception:
            pass
        self.destroy()

    # ---------- Configuración (diálogo con SCROLL) ----------

    def _open_config_dialog(self):
        dlg = tk.Toplevel(self)
        dlg.title("Configuración")
        dlg.geometry("760x700")
        dlg.transient(self)
        dlg.grab_set()

        # Contenedor desplazable
        sframe = ScrollableFrame(dlg)
        sframe.pack(fill=tk.BOTH, expand=True)

        frm = sframe.inner  # aquí ponemos todos los campos

        # --- Secciones con Labelframe para orden ---
        lf_paths = ttk.Labelframe(frm, text="Rutas y tipo de servidor", padding=10)
        lf_paths.pack(fill=tk.X, padx=10, pady=6)

        # Carpeta del servidor
        row = 0
        ttk.Label(lf_paths, text="Carpeta del servidor:").grid(row=row, column=0, sticky="w")
        var_dir = tk.StringVar(value=self.server_dir)
        e_dir = ttk.Entry(lf_paths, textvariable=var_dir, width=48)
        e_dir.grid(row=row, column=1, sticky="ew", padx=6)
        ttk.Button(lf_paths, text="Cambiar...", command=lambda: self._pick_dir(var_dir)).grid(row=row, column=2, padx=4)
        lf_paths.columnconfigure(1, weight=1); row += 1

        # Java
        ttk.Label(lf_paths, text="Ruta de Java:").grid(row=row, column=0, sticky="w")
        var_java = tk.StringVar(value=self.app_config.get("java_path", "java"))
        e_java = ttk.Entry(lf_paths, textvariable=var_java, width=48)
        e_java.grid(row=row, column=1, sticky="ew", padx=6)
        ttk.Button(lf_paths, text="Buscar...", command=lambda: self._pick_file(var_java)).grid(row=row, column=2, padx=4)
        row += 1

        # Tipo
        ttk.Label(lf_paths, text="Tipo de servidor:").grid(row=row, column=0, sticky="w")
        server_types = ["vanilla", "forge"]
        var_server_type = tk.StringVar(value=self.app_config.get("server_type", "vanilla"))
        cb_server_type = ttk.Combobox(lf_paths, textvariable=var_server_type, values=server_types, state="readonly")
        cb_server_type.grid(row=row, column=1, sticky="w", padx=6); row += 1

        # Versiones
        ttk.Label(lf_paths, text="Versión de Minecraft:").grid(row=row, column=0, sticky="w")
        var_mc_version = tk.StringVar(value=self.app_config.get("mc_version", "latest-release"))
        cb_versions = ttk.Combobox(lf_paths, textvariable=var_mc_version, state="readonly")
        cb_versions.grid(row=row, column=1, sticky="ew", padx=6)
        ttk.Button(lf_paths, text="Actualizar", command=lambda: self._fill_versions(cb_versions)).grid(row=row, column=2, padx=4); row += 1

        forge_row = ttk.Frame(lf_paths)
        forge_row.grid(row=row, column=0, columnspan=3, sticky="ew", pady=(4,0))
        ttk.Label(forge_row, text="Versión de Forge:").grid(row=0, column=0, sticky="w")
        var_forge_version = tk.StringVar(value=self.app_config.get("forge_version", ""))
        cb_forge_versions = ttk.Combobox(forge_row, textvariable=var_forge_version, state="readonly", width=40)
        cb_forge_versions.grid(row=0, column=1, sticky="ew", padx=6)
        ttk.Button(forge_row, text="Actualizar", command=lambda: self._fill_forge_versions(var_mc_version, cb_forge_versions)).grid(row=0, column=2, padx=4)
        forge_row.columnconfigure(1, weight=1)

        def on_server_type_change(_evt=None):
            if var_server_type.get() == "forge":
                forge_row.grid()
                self._fill_forge_versions(var_mc_version, cb_forge_versions)
            else:
                forge_row.grid_remove()
        cb_server_type.bind("<<ComboboxSelected>>", on_server_type_change)

        # Red y memoria
        lf_perf = ttk.Labelframe(frm, text="Rendimiento y Red", padding=10)
        lf_perf.pack(fill=tk.X, padx=10, pady=6)
        ttk.Label(lf_perf, text="Puerto local (25565):").grid(row=0, column=0, sticky="w")
        var_port = tk.StringVar(value=str(self.app_config.get("server_port", 25565)))
        ttk.Entry(lf_perf, textvariable=var_port, width=10).grid(row=0, column=1, sticky="w", padx=6)
        ttk.Label(lf_perf, text="RAM mínima (Xms):").grid(row=1, column=0, sticky="w")
        var_ram_min = tk.StringVar(value=self.app_config.get("ram_min", "1G"))
        ttk.Entry(lf_perf, textvariable=var_ram_min, width=10).grid(row=1, column=1, sticky="w", padx=6)
        ttk.Label(lf_perf, text="RAM máxima (Xmx):").grid(row=2, column=0, sticky="w")
        var_ram_max = tk.StringVar(value=self.app_config.get("ram_max", "2G"))
        ttk.Entry(lf_perf, textvariable=var_ram_max, width=10).grid(row=2, column=1, sticky="w", padx=6)

        # playit
        lf_playit = ttk.Labelframe(frm, text="playit.gg (túnel)", padding=10)
        lf_playit.pack(fill=tk.X, padx=10, pady=6)
        ttk.Label(lf_playit, text="Ruta agente:").grid(row=0, column=0, sticky="w")
        var_playit = tk.StringVar(value=self.app_config.get("playit_path", ""))
        ttk.Entry(lf_playit, textvariable=var_playit).grid(row=0, column=1, sticky="ew", padx=6)
        ttk.Button(lf_playit, text="Buscar...", command=lambda: self._pick_file(var_playit)).grid(row=0, column=2, padx=4)
        lf_playit.columnconfigure(1, weight=1)
        var_auto_playit = tk.BooleanVar(value=self.app_config.get("auto_start_playit", True))
        ttk.Checkbutton(lf_playit, text="Iniciar automáticamente cuando el servidor esté listo",
                        variable=var_auto_playit).grid(row=1, column=0, columnspan=3, sticky="w", pady=(6,0))

        # Props del servidor
        lf_props = ttk.Labelframe(frm, text="Propiedades del servidor (principales)", padding=10)
        lf_props.pack(fill=tk.X, padx=10, pady=6)
        prop_fields = [
            ("max-players", "Máx. jugadores"),
            ("difficulty", "Dificultad (peaceful/easy/normal/hard)"),
            ("gamemode", "Gamemode (survival/creative/adventure/spectator)"),
            ("online-mode", "Online mode (true/false)"),
            ("white-list", "Whitelist (true/false)"),
            ("enable-command-block", "Command block (true/false)"),
            ("level-name", "Nombre del mundo"),
            ("level-seed", "Semilla"),
            ("motd", "MOTD"),
        ]
        prop_vars = {}
        r = 0
        difficulty_var = None
        difficulty_entry = None
        for key, label in prop_fields:
            ttk.Label(lf_props, text=label + ":").grid(row=r, column=0, sticky="w", pady=2)
            var = tk.StringVar(value=self.server_properties.get(key, DEFAULT_SERVER_PROPERTIES.get(key, "")))
            ent = ttk.Entry(lf_props, textvariable=var)
            ent.grid(row=r, column=1, sticky="ew", padx=6, pady=2)
            prop_vars[key] = var
            if key == "difficulty":
                difficulty_var = var
                difficulty_entry = ent
            r += 1
        lf_props.columnconfigure(1, weight=1)

        var_hardcore = tk.BooleanVar(value=(self.server_properties.get("hardcore", "false").lower() == "true"))
        def _toggle_hardcore():
            if var_hardcore.get():
                if difficulty_var is not None:
                    difficulty_var.set("hard")
                if difficulty_entry is not None:
                    difficulty_entry.configure(state="disabled")
            else:
                if difficulty_entry is not None:
                    difficulty_entry.configure(state="normal")
        ttk.Checkbutton(lf_props, text="Hardcore (banea al morir; fuerza dificultad 'hard')",
                        variable=var_hardcore, command=_toggle_hardcore).grid(row=r, column=0, columnspan=2, sticky="w", pady=(6,0))
        _toggle_hardcore()

        # RCON
        lf_rcon = ttk.Labelframe(frm, text="RCON (para enviar comandos si el server no fue lanzado por la app)", padding=10)
        lf_rcon.pack(fill=tk.X, padx=10, pady=6)
        var_rcon_enable = tk.BooleanVar(value=self.app_config.get("enable_rcon", True))
        ttk.Checkbutton(lf_rcon, text="Habilitar y auto-configurar server.properties",
                        variable=var_rcon_enable).grid(row=0, column=0, columnspan=3, sticky="w")
        ttk.Label(lf_rcon, text="Puerto:").grid(row=1, column=0, sticky="w")
        var_rcon_port = tk.StringVar(value=str(self.app_config.get("rcon_port", 25575)))
        ttk.Entry(lf_rcon, textvariable=var_rcon_port, width=10).grid(row=1, column=1, sticky="w", padx=6)
        ttk.Label(lf_rcon, text="Contraseña:").grid(row=2, column=0, sticky="w")
        var_rcon_pass = tk.StringVar(value=self.app_config.get("rcon_password", "minecraft"))
        ttk.Entry(lf_rcon, textvariable=var_rcon_pass, show="•").grid(row=2, column=1, sticky="w", padx=6)

        # Optimización
        lf_opt = ttk.Labelframe(frm, text="Optimización", padding=10)
        lf_opt.pack(fill=tk.X, padx=10, pady=6)
        var_jvm_opt = tk.BooleanVar(value=self.app_config.get("enable_jvm_optim", True))
        ttk.Checkbutton(lf_opt, text="Flags JVM (G1GC / pausas bajas)", variable=var_jvm_opt).grid(row=0, column=0, sticky="w")
        var_prop_opt = tk.BooleanVar(value=self.app_config.get("enable_opt_properties", True))
        ttk.Checkbutton(lf_opt, text="Ajustes recomendados en server.properties", variable=var_prop_opt).grid(row=1, column=0, sticky="w")
        var_use_pty = tk.BooleanVar(value=self.app_config.get("use_pty_on_unix", True))
        ttk.Checkbutton(lf_opt, text="Usar PTY en Linux/macOS (mejora consola)", variable=var_use_pty).grid(row=2, column=0, sticky="w")

        # Autosave
        lf_save = ttk.Labelframe(frm, text="Autosave", padding=10)
        lf_save.pack(fill=tk.X, padx=10, pady=6)
        var_autosave = tk.BooleanVar(value=self.app_config.get("enable_autosave", True))
        ttk.Checkbutton(lf_save, text="Habilitar autosave", variable=var_autosave).grid(row=0, column=0, sticky="w")
        ttk.Label(lf_save, text="Cada (minutos):").grid(row=1, column=0, sticky="w")
        var_autosave_min = tk.StringVar(value=str(self.app_config.get("autosave_minutes", 10)))
        ttk.Entry(lf_save, textvariable=var_autosave_min, width=10).grid(row=1, column=1, sticky="w", padx=6)

        # Botones
        btns = ttk.Frame(dlg, padding=8)
        btns.pack(fill=tk.X, side=tk.BOTTOM)
        ttk.Button(btns, text="Cancelar", command=dlg.destroy).pack(side=tk.RIGHT, padx=6)
        ttk.Button(btns, text="Guardar",
                   command=lambda: self._save_config_from_dialog(
                       dlg, var_dir, var_java, var_server_type, cb_versions, var_forge_version, var_port,
                       var_ram_min, var_ram_max, var_playit, var_auto_playit,
                       prop_vars, var_hardcore, difficulty_var,
                       var_rcon_enable, var_rcon_port, var_rcon_pass,
                       var_jvm_opt, var_prop_opt, var_use_pty,
                       var_autosave, var_autosave_min
                   )).pack(side=tk.RIGHT, padx=6)

        # Inicializar versiones
        self._fill_versions(cb_versions, preselect=self.app_config.get("mc_version", "latest-release"))
        on_server_type_change()

    def _fill_versions(self, combobox: ttk.Combobox, preselect: str = "latest-release"):
        try:
            if not self.manifest_cache:
                self.manifest_cache = fetch_manifest()
            versions = self.manifest_cache.get("versions", [])
            items = ["latest-release", "latest-snapshot"]
            releases = [v["id"] for v in versions if v.get("type") == "release"]
            snapshots = [v["id"] for v in versions if v.get("type") == "snapshot"]
            items.extend(releases[:200])
            items.extend(snapshots[:50])
            combobox["values"] = items
            if preselect in items:
                combobox.set(preselect)
            else:
                combobox.set("latest-release")
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo cargar manifest de versiones:\n{e}")
            combobox["values"] = ["latest-release"]
            combobox.set("latest-release")

    def _fill_forge_versions(self, mc_version_var: tk.StringVar, cb_forge: ttk.Combobox):
        try:
            mc_version = mc_version_var.get()
            if mc_version in ["latest-release", "latest-snapshot"]:
                if not self.manifest_cache:
                    self.manifest_cache = fetch_manifest()
                latest_key = "release" if mc_version == "latest-release" else "snapshot"
                mc_version = self.manifest_cache.get("latest", {}).get(latest_key, "")
            # Fuente alternativa ligera (solo placeholder si falla)
            # Aquí podrías integrar más fuentes si hace falta.
            cb_forge["values"] = [f"{mc_version}-recommended", f"{mc_version}-latest"]
            cb_forge.set(cb_forge["values"][0])
        except Exception as e:
            cb_forge["values"] = [f"Error: {e}"]
            cb_forge.set(f"Error: {e}")

    def _pick_dir(self, var: tk.StringVar):
        d = filedialog.askdirectory(title="Selecciona carpeta del servidor")
        if d:
            var.set(d)

    def _pick_file(self, var: tk.StringVar):
        f = filedialog.askopenfilename(title="Selecciona archivo ejecutable")
        if f:
            var.set(f)

    def _save_config_from_dialog(self, dlg,
                                 var_dir, var_java, var_server_type, cb_versions, var_forge_version, var_port,
                                 var_ram_min, var_ram_max, var_playit, var_auto_playit,
                                 prop_vars, var_hardcore: tk.BooleanVar, difficulty_var: tk.StringVar,
                                 var_rcon_enable: tk.BooleanVar, var_rcon_port: tk.StringVar, var_rcon_pass: tk.StringVar,
                                 var_jvm_opt: tk.BooleanVar, var_prop_opt: tk.BooleanVar, var_use_pty: tk.BooleanVar,
                                 var_autosave: tk.BooleanVar, var_autosave_min: tk.StringVar):
        try:
            port = int(var_port.get().strip())
            if not (1 <= port <= 65535):
                raise ValueError("Puerto inválido.")

            self.app_config["server_dir"] = var_dir.get().strip() or self.server_dir
            self.app_config["java_path"] = var_java.get().strip() or "java"
            self.app_config["server_type"] = var_server_type.get().strip() or "vanilla"
            self.app_config["mc_version"] = cb_versions.get().strip() or "latest-release"
            self.app_config["forge_version"] = var_forge_version.get().strip() if var_server_type.get() == "forge" else ""
            self.app_config["server_port"] = port
            self.app_config["ram_min"] = var_ram_min.get().strip() or "1G"
            self.app_config["ram_max"] = var_ram_max.get().strip() or "2G"
            self.app_config["playit_path"] = var_playit.get().strip()
            self.app_config["auto_start_playit"] = bool(var_auto_playit.get())

            # RCON
            self.app_config["enable_rcon"] = bool(var_rcon_enable.get())
            self.app_config["rcon_port"] = int(var_rcon_port.get().strip() or "25575")
            self.app_config["rcon_password"] = var_rcon_pass.get().strip() or "minecraft"

            # Optimizaciones
            self.app_config["enable_jvm_optim"] = bool(var_jvm_opt.get())
            self.app_config["enable_opt_properties"] = bool(var_prop_opt.get())
            self.app_config["use_pty_on_unix"] = bool(var_use_pty.get())

            # Autosave
            self.app_config["enable_autosave"] = bool(var_autosave.get())
            self.app_config["autosave_minutes"] = int(var_autosave_min.get().strip() or "10")

            # Guardar properties
            for key, v in prop_vars.items():
                self.server_properties[key] = v.get().strip()
            self.server_properties["server-port"] = str(self.app_config["server_port"])
            self.server_properties["hardcore"] = "true" if var_hardcore.get() else "false"
            if var_hardcore.get():
                self.server_properties["difficulty"] = "hard"
                if difficulty_var is not None:
                    difficulty_var.set("hard")

            self._save_app_config()
            self._save_server_properties()
            self._refresh_status_labels()
            self._log_sys("Configuración guardada.")
            dlg.destroy()
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo guardar configuración:\n{e}")

    # ---------- Ayuda ----------

    def _show_help(self):
        text = (
            "AYUDA RÁPIDA\n\n"
            "1) Crear Servidor: descarga el JAR oficial (Vanilla) o instala Forge (si elegiste Forge), acepta EULA y genera el mundo.\n"
            "2) Iniciar Servidor: verás todos los logs y chat en la consola. Puedes enviar comandos desde el cuadro inferior.\n"
            "3) Túnel playit.gg: pulsa 'Iniciar playit.gg'. Se mostrarán enlaces públicos priorizando *.joinmc.link.\n"
            "4) RCON: si inicias tu server fuera de la app, habilita RCON en 'Configurar' para poder enviar comandos desde aquí.\n"
            "5) Hardcore: actívalo en 'Propiedades'; fuerza difficulty=hard automáticamente.\n"
            "6) Optimiza: ajusta Xms/Xmx y flags JVM en 'Rendimiento y Red' / 'Optimización'.\n"
            "7) Autosave: ejecuta 'save-all flush' automáticamente cada N minutos.\n"
            "8) Backups: usa 'Archivo → Crear/Restaurar backup' para proteger tu mundo.\n"
            "9) Filtros: oculta logs INFO con la casilla en la barra inferior.\n"
        )
        messagebox.showinfo("Ayuda", text)

    def _show_about(self):
        messagebox.showinfo("Acerca de", f"{APP_NAME}\n\n"
                                         "Gestor rápido y claro para servidores de Minecraft.\n"
                                         "Vanilla/Forge, túnel playit.gg, consola robusta, RCON y más.\n"
                                         "Licencia: MIT")


# ------------------------------------------------------------------------------
# Main
# ------------------------------------------------------------------------------

def main():
    app = MinecraftGUI()
    app.mainloop()


if __name__ == "__main__":
    main()