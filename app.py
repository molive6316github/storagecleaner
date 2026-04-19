import os
import re
import sys
import math
import json
import hashlib
import threading
import webbrowser
import mimetypes
from pathlib import Path
from datetime import datetime, timedelta
from flask import Flask, jsonify, request, render_template, send_file

try:
    import send2trash
    HAS_TRASH = True
except ImportError:
    HAS_TRASH = False

# ── Path helpers (PyInstaller-aware) ─────────────────────────────────────────

def _bundle_dir() -> str:
    """Directory that contains bundled data files (templates, etc.)."""
    if getattr(sys, "frozen", False):
        return sys._MEIPASS          # type: ignore[attr-defined]
    return os.path.dirname(os.path.abspath(__file__))

def _app_dir() -> str:
    """Writable directory next to the running exe (or script during dev)."""
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))

app = Flask(__name__, template_folder=os.path.join(_bundle_dir(), "templates"))

_lock = threading.Lock()
CONFIG_FILE = os.path.join(_app_dir(), "storage_cleaner_config.json")
MIN_SIZE = 500 * 1024
SKIP_DIRS = {"$recycle.bin", "system volume information", "windows",
             "program files", "program files (x86)", "programdata"}

# ── Global state ─────────────────────────────────────────────────────────────

state = {
    "files": [], "scanning": False, "scan_done": False,
    "ai_done": False, "current_dir": "", "scanned_count": 0,
    "error": None, "folder_stats": [],
}

dup_state = {
    "scanning": False, "done": False, "groups": [],
    "progress": 0, "total": 0, "error": None,
}

sched_state = {
    "enabled": False, "interval_hours": 24,
    "last_run": None, "next_run": None,
}

_sched_timer = None

# ── Config ────────────────────────────────────────────────────────────────────

def load_config():
    if os.path.exists(CONFIG_FILE):
        try:
            data = json.loads(open(CONFIG_FILE).read())
            sched_state.update(data.get("schedule", {}))
        except Exception:
            pass

def save_config():
    try:
        open(CONFIG_FILE, "w").write(json.dumps({"schedule": dict(sched_state)}, indent=2))
    except Exception:
        pass

load_config()

# ── Helpers ───────────────────────────────────────────────────────────────────

def get_scan_dirs():
    home = os.path.expanduser("~")
    candidates = [
        os.path.join(home, d) for d in
        ("Downloads", "Desktop", "Documents", "Pictures", "Videos", "Music")
    ]
    for env in ("TEMP", "TMP"):
        v = os.environ.get(env, "")
        if v:
            candidates.append(v)
    local = os.environ.get("LOCALAPPDATA", "")
    if local:
        candidates.append(os.path.join(local, "Temp"))
    return [d for d in candidates if d and os.path.exists(d)]


def categorize(name):
    ext = Path(name).suffix.lower()
    if ext in {".mp4", ".avi", ".mov", ".mkv", ".wmv", ".flv", ".webm", ".m4v"}:
        return "video"
    if ext in {".mp3", ".wav", ".flac", ".aac", ".m4a", ".ogg", ".wma", ".opus"}:
        return "audio"
    if ext in {".jpg", ".jpeg", ".png", ".gif", ".bmp", ".tiff", ".webp", ".heic"}:
        return "image"
    if ext in {".pdf", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx", ".txt"}:
        return "document"
    if ext in {".zip", ".rar", ".7z", ".tar", ".gz", ".bz2", ".xz", ".iso"}:
        return "archive"
    if ext in {".exe", ".msi", ".dmg", ".pkg", ".deb", ".rpm", ".appx"}:
        return "installer"
    if ext in {".tmp", ".temp", ".cache", ".log", ".bak", ".old", ".dmp"}:
        return "temp"
    return "other"


def compute_hash(path, chunk=65536):
    h = hashlib.md5()
    try:
        with open(path, "rb") as f:
            while True:
                buf = f.read(chunk)
                if not buf:
                    break
                h.update(buf)
        return h.hexdigest()
    except (OSError, PermissionError):
        return None


# ── PRISM: Priority Removal Index Score Matrix ────────────────────────────────
#
# Four independent signal axes scored 0–100, combined via weighted sum.
# Final score ≥ 55 → DELETE (high / medium), < 35 → KEEP, middle → lean KEEP.

_RE_TEMP_NAME = re.compile(
    r'(?:^|[\s_\-.])'
    r'(?:temp|tmp|cache|bak|backup|old|orig|copy|swap|swp|dmp|crash|dump|partial|incomplete)'
    r'(?:[\s_\-.]|$)',
    re.IGNORECASE,
)
_RE_VERSION_COPY = re.compile(
    r'(?:\s*\(\d+\)\s*$|[\s_\-]v\d[\d.]*[\s_\-]|_\d{8}(?:_\d{6})?$|\s+copy\s*\d*$|[\s_\-]copy[\s_\-])',
    re.IGNORECASE,
)
_RE_INSTALLER = re.compile(
    r'(?:setup|install(?:er)?|update|patch|hotfix|redistrib|vcredist|directx|runtime|service.?pack)',
    re.IGNORECASE,
)
_RE_LOG_EXT = re.compile(r'\.(log|log\.\d+|out|err|trace|debug|audit)\d*$', re.IGNORECASE)
_RE_CRASH   = re.compile(r'(?:crash|dump|minidump|memory\.dmp)', re.IGNORECASE)

# Protected path fragments — never suggest deleting these
_PROTECTED_SEGS = {
    "\\windows\\", "/windows/",
    "\\program files", "/program files",
    "\\system32\\", "\\syswow64\\",
    "\\boot\\",     "/boot/",
}

# Category-specific age half-lives (days): time until age contributes full weight
_HALF_LIFE = {
    "temp":      7,
    "installer": 45,
    "archive":   120,
    "video":     180,
    "audio":     180,
    "image":     365,
    "document":  730,
    "other":     90,
}


def prism_score(f: dict) -> tuple[str, str, str]:
    """
    Compute PRISM score and return (recommendation, reason, confidence).

    Score axes:
      T — Temporal   (0–40)  age × access-recency penalty
      S — Spatial    (0–25)  path-based location analysis
      E — sEmantic   (0–20)  name patterns + category signals
      M — Mass       (0–15)  log-scaled size benefit

    Confidence: derived from score margin and supporting evidence count.
    """
    name      = f["name"]
    ext       = Path(name).suffix.lower()
    path_low  = f["path"].replace("/", "\\").lower()
    cat       = f["category"]
    size      = f["size"]
    days_mod  = f["days_old"]
    days_acc  = f.get("days_accessed", days_mod)

    evidence: list[str] = []
    score = 0.0

    # ── T: Temporal (0–40) ────────────────────────────────────────────────────
    half = _HALF_LIFE.get(cat, 90)
    # Logistic growth: 0 when brand-new, saturates near 20 for very old files
    t        = days_mod / half
    age_raw  = 20.0 * (2.0 / (1.0 + math.exp(-2.0 * t)) - 1.0)
    age_pts  = max(0.0, age_raw)                          # 0 … 20

    # Access-recency penalty: up to 20 pts subtracted if opened recently
    # Decays with time-constant 21 days: fully penalised at <7 days
    acc_penalty = 20.0 * math.exp(-days_acc / 21.0)       # 0 … 20

    temporal = max(0.0, age_pts - acc_penalty)
    temporal = min(temporal, 40.0)
    score   += temporal

    if days_mod > half:
        evidence.append(f"{days_mod}d since modified")
    if days_acc < 14:
        evidence.append(f"opened {days_acc}d ago")

    # ── S: Spatial (0–25) ────────────────────────────────────────────────────
    if any(seg in path_low for seg in ("\\temp\\", "\\tmp\\", "appdata\\local\\temp")):
        spatial = 25.0
        evidence.append("system temp folder")
    elif "\\downloads\\" in path_low:
        spatial = 15.0
        evidence.append("Downloads folder")
    elif "\\appdata\\" in path_low:
        spatial = 8.0
    elif any(seg in path_low for seg in ("\\documents\\", "\\pictures\\", "\\music\\")):
        spatial = -10.0   # personal content — lean keep
    else:
        spatial = 0.0
    score += max(-10.0, spatial)

    # ── E: sEmantic (0–20) ────────────────────────────────────────────────────
    sem = 0.0

    # Category-level baseline
    CAT_SEM = {"temp": 20, "installer": 12, "archive": 4,
               "video": 2, "audio": 2, "image": 0, "document": -5, "other": 3}
    sem += CAT_SEM.get(cat, 0)

    # Name pattern signals (additive, capped)
    if _RE_TEMP_NAME.search(name):
        sem += 8
        evidence.append("temp/backup name")
    if _RE_VERSION_COPY.search(name):
        sem += 5
        evidence.append("duplicate/versioned copy")
    if cat == "installer" and _RE_INSTALLER.search(name):
        sem += 4
        evidence.append("installer package")
    if _RE_LOG_EXT.search(name) or ext in {".log", ".out", ".err", ".trace"}:
        sem = max(sem, 16)
        evidence.append("log file")
    if ext in {".dmp", ".mdmp", ".hdmp"} or _RE_CRASH.search(name):
        sem = max(sem, 18)
        evidence.append("crash dump")
    if ext == ".iso":
        sem = max(sem, 10)
        evidence.append("disk image")

    score += max(-5.0, min(20.0, sem))

    # ── M: Mass (0–15) ────────────────────────────────────────────────────────
    # log₂(size_mb / 10) scaled so 10 MB → ~0, 100 MB → ~6.6, 1 GB → ~13
    size_mb = size / (1024 * 1024)
    mass = min(15.0, max(0.0, 4.0 * math.log2(max(1.0, size_mb / 10.0))))
    score += mass
    if size_mb >= 200:
        evidence.append(f"{size_mb:,.0f} MB")

    # ── Hard overrides ────────────────────────────────────────────────────────
    if days_mod < 3:
        score = min(score, 12.0)
        evidence = [f"only {days_mod}d old — keeping safe"]

    if any(seg in path_low for seg in _PROTECTED_SEGS):
        score = 0.0
        evidence = ["protected system path"]

    # ── Decision ─────────────────────────────────────────────────────────────
    score = max(0.0, min(100.0, score))

    # Confidence: high when far from threshold (55), or many signals agree
    margin = abs(score - 55.0)
    n_ev   = len(evidence)
    if margin >= 25 or (margin >= 15 and n_ev >= 2):
        confidence = "high"
    elif margin >= 10 or n_ev >= 2:
        confidence = "medium"
    else:
        confidence = "low"

    action = "DELETE" if score >= 55.0 else "KEEP"

    # Build human reason
    if evidence:
        joined = "; ".join(evidence[:3])
        reason = (f"Flagged for removal — {joined}."
                  if action == "DELETE" else
                  f"Recommended to keep — {joined}.")
    else:
        reason = ("Multiple weak deletion signals." if action == "DELETE"
                  else "No strong removal signals — keeping safe.")

    return action, reason, confidence


# ── Main scan ─────────────────────────────────────────────────────────────────

def do_scan():
    with _lock:
        state.update({"scanning": True, "files": [], "scanned_count": 0,
                       "scan_done": False, "ai_done": False, "error": None, "folder_stats": []})

    seen, candidates, folder_bytes = set(), [], {}

    for directory in get_scan_dirs():
        with _lock:
            state["current_dir"] = directory
        try:
            for root, dirs, files in os.walk(directory, topdown=True):
                dirs[:] = [d for d in dirs
                           if not d.startswith(".") and d.lower() not in SKIP_DIRS
                           and not os.path.islink(os.path.join(root, d))]
                for fname in files:
                    fpath = os.path.normpath(os.path.join(root, fname))
                    if fpath in seen:
                        continue
                    seen.add(fpath)
                    try:
                        s = os.stat(fpath)
                        rel   = os.path.relpath(fpath, directory)
                        parts = rel.split(os.sep)
                        depth = min(len(parts) - 1, 2)
                        folder_key = os.path.join(directory, *parts[:depth]) if depth else directory
                        folder_bytes[folder_key] = folder_bytes.get(folder_key, 0) + s.st_size

                        if s.st_size < MIN_SIZE:
                            continue
                        mtime = datetime.fromtimestamp(s.st_mtime)
                        atime = datetime.fromtimestamp(s.st_atime)
                        days_mod = max(0, (datetime.now() - mtime).days)
                        days_acc = max(0, (datetime.now() - atime).days)
                        candidates.append({
                            "path": fpath, "name": fname,
                            "size": s.st_size, "size_mb": round(s.st_size / (1024 * 1024), 1),
                            "modified":      mtime.strftime("%b %d, %Y"),
                            "accessed":      atime.strftime("%b %d, %Y"),
                            "days_old":      days_mod,
                            "days_accessed": days_acc,
                            "category":      categorize(fname),
                            "recommendation": None, "reason": "", "confidence": "low",
                        })
                        with _lock:
                            state["scanned_count"] += 1
                    except (OSError, PermissionError):
                        continue
        except (OSError, PermissionError):
            continue

    folder_list = sorted(
        [{"path": k, "name": os.path.relpath(k, os.path.expanduser("~")),
          "size": v, "size_mb": round(v / (1024 * 1024), 1)}
         for k, v in folder_bytes.items()],
        key=lambda x: x["size"], reverse=True
    )[:20]

    candidates.sort(key=lambda f: f["size"] * (1 + f["days_old"] / 30), reverse=True)
    candidates = candidates[:150]

    # ── Score every candidate with PRISM (microseconds per file) ─────────────
    for f in candidates:
        action, reason, confidence = prism_score(f)
        f.update({"recommendation": action, "reason": reason, "confidence": confidence})

    with _lock:
        state["files"]        = candidates
        state["folder_stats"] = folder_list
        state["scan_done"]    = True
        state["ai_done"]      = True
        state["scanning"]     = False
        sched_state["last_run"] = datetime.now().isoformat()
    save_config()


# ── Duplicate scan ────────────────────────────────────────────────────────────

def do_dup_scan():
    with _lock:
        dup_state.update({"scanning": True, "done": False, "groups": [],
                           "progress": 0, "total": 0, "error": None})

    size_map = {}
    for directory in get_scan_dirs():
        try:
            for root, dirs, files in os.walk(directory, topdown=True):
                dirs[:] = [d for d in dirs
                           if not d.startswith(".") and d.lower() not in SKIP_DIRS]
                for fname in files:
                    fpath = os.path.normpath(os.path.join(root, fname))
                    try:
                        s = os.stat(fpath)
                        if s.st_size >= MIN_SIZE:
                            size_map.setdefault(s.st_size, []).append((fpath, s))
                    except (OSError, PermissionError):
                        continue
        except (OSError, PermissionError):
            continue

    to_hash = [(p, s) for paths in size_map.values() if len(paths) > 1 for p, s in paths]
    with _lock:
        dup_state["total"] = len(to_hash)

    hash_map = {}
    for i, (fpath, stat_info) in enumerate(to_hash):
        with _lock:
            dup_state["progress"] = i + 1
        h = compute_hash(fpath)
        if h:
            hash_map.setdefault((stat_info.st_size, h), []).append((fpath, stat_info))

    groups = []
    for (size, _), items in hash_map.items():
        if len(items) < 2:
            continue
        file_entries = []
        for fpath, s in items:
            mtime = datetime.fromtimestamp(s.st_mtime)
            file_entries.append({
                "path": fpath, "name": os.path.basename(fpath),
                "size": size, "size_mb": round(size / (1024 * 1024), 1),
                "modified": mtime.strftime("%b %d, %Y"),
                "days_old": max(0, (datetime.now() - mtime).days),
            })
        file_entries.sort(key=lambda x: x["days_old"])
        groups.append({
            "size": size, "size_mb": round(size / (1024 * 1024), 1),
            "count": len(file_entries),
            "wasted_bytes": size * (len(file_entries) - 1),
            "wasted_mb": round(size * (len(file_entries) - 1) / (1024 * 1024), 1),
            "files": file_entries,
        })

    groups.sort(key=lambda g: g["wasted_bytes"], reverse=True)
    with _lock:
        dup_state.update({"scanning": False, "done": True, "groups": groups})


# ── Scheduler ─────────────────────────────────────────────────────────────────

def _run_scheduled():
    print(f"[Scheduler] Auto-scan at {datetime.now():%Y-%m-%d %H:%M}")
    t = threading.Thread(target=do_scan, daemon=True)
    t.start()
    t.join()
    _schedule_next()


def _schedule_next():
    global _sched_timer
    if not sched_state["enabled"]:
        return
    delay = sched_state["interval_hours"] * 3600
    sched_state["next_run"] = (datetime.now() + timedelta(hours=sched_state["interval_hours"])).isoformat()
    save_config()
    _sched_timer = threading.Timer(delay, _run_scheduled)
    _sched_timer.daemon = True
    _sched_timer.start()


if sched_state["enabled"] and sched_state.get("next_run"):
    try:
        next_t = datetime.fromisoformat(sched_state["next_run"])
        delay  = max(60, (next_t - datetime.now()).total_seconds())
        _sched_timer = threading.Timer(delay, _run_scheduled)
        _sched_timer.daemon = True
        _sched_timer.start()
        print(f"[Scheduler] Resuming — next scan in {delay/3600:.1f}h")
    except Exception:
        _schedule_next()


# ── Routes ────────────────────────────────────────────────────────────────────

@app.route("/")
def index():
    return render_template("index.html")


@app.route("/api/start", methods=["POST"])
def start_scan():
    with _lock:
        if state["scanning"] and not state["scan_done"]:
            return jsonify({"ok": False, "msg": "Already scanning"})
    threading.Thread(target=do_scan, daemon=True).start()
    return jsonify({"ok": True})


@app.route("/api/status")
def status():
    with _lock:
        return jsonify({
            "scanning":     state["scanning"],
            "scan_done":    state["scan_done"],
            "ai_done":      state["ai_done"],
            "scanned_count": state["scanned_count"],
            "file_count":   len(state["files"]),
            "current_dir":  state["current_dir"],
            "error":        state["error"],
        })


@app.route("/api/files")
def get_files():
    with _lock:
        return jsonify(state["files"])


@app.route("/api/folder-stats")
def folder_stats():
    with _lock:
        return jsonify(state["folder_stats"])


@app.route("/api/preview")
def preview_file():
    path = request.args.get("path", "")
    if not path:
        return "Missing path", 400
    abs_path = os.path.normpath(os.path.abspath(path))
    if not os.path.isfile(abs_path):
        return "Not found", 404
    allowed = [os.path.normpath(os.path.abspath(d)) for d in get_scan_dirs()]
    if not any(abs_path.startswith(d + os.sep) or abs_path == d for d in allowed):
        return "Forbidden", 403
    mime = mimetypes.guess_type(abs_path)[0] or "application/octet-stream"
    return send_file(abs_path, mimetype=mime)


@app.route("/api/delete", methods=["POST"])
def delete_files():
    data = request.get_json(force=True)
    paths = data.get("paths", [])
    results, total_freed = [], 0
    for path in paths:
        try:
            size = os.path.getsize(path) if os.path.exists(path) else 0
            if HAS_TRASH:
                send2trash.send2trash(path)
            else:
                os.remove(path)
            total_freed += size
            results.append({"path": path, "ok": True})
        except Exception as ex:
            results.append({"path": path, "ok": False, "error": str(ex)})
    return jsonify({"results": results, "freed_bytes": total_freed})


@app.route("/api/duplicates/start", methods=["POST"])
def start_dup_scan():
    with _lock:
        if dup_state["scanning"]:
            return jsonify({"ok": False, "msg": "Already scanning"})
    threading.Thread(target=do_dup_scan, daemon=True).start()
    return jsonify({"ok": True})


@app.route("/api/duplicates/status")
def dup_status():
    with _lock:
        return jsonify({
            "scanning":   dup_state["scanning"], "done": dup_state["done"],
            "progress":   dup_state["progress"], "total": dup_state["total"],
            "group_count": len(dup_state["groups"]),
        })


@app.route("/api/duplicates")
def get_duplicates():
    with _lock:
        return jsonify(dup_state["groups"])


@app.route("/api/schedule", methods=["GET"])
def get_schedule():
    with _lock:
        return jsonify(dict(sched_state))


@app.route("/api/schedule", methods=["POST"])
def set_schedule():
    global _sched_timer
    data = request.get_json(force=True)
    with _lock:
        sched_state["enabled"]        = bool(data.get("enabled", False))
        sched_state["interval_hours"] = max(1, int(data.get("interval_hours", 24)))
    if _sched_timer:
        _sched_timer.cancel()
        _sched_timer = None
    if sched_state["enabled"]:
        _schedule_next()
    else:
        sched_state["next_run"] = None
        save_config()
    return jsonify({"ok": True, "state": dict(sched_state)})


if __name__ == "__main__":
    import threading
    threading.Timer(1.5, lambda: webbrowser.open("http://localhost:5001")).start()
    print("🧹 Storage Cleaner starting at http://localhost:5001")
    app.run(port=5001, debug=False)
