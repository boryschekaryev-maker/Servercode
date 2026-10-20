#!/usr/bin/env python3
"""
PyVM - a tiny virtual machine / desktop environment built with pygame.

Run:      python pyvm.py
Install:  pip install pygame-ce        (plain `pygame` works too if it has wheels for your Python)

Apps: Terminal, Files, Notepad, Calculator, Clock (clock/stopwatch/timer), Browser.
The Browser is real Chromium (JavaScript, video, logins...). One-time setup for it:
    pip install -U playwright
    playwright install chromium
Without it, a basic text-only browser is offered as a fallback.
The virtual disk is stored next to this script in vm_disk.json.
"""
import ast, base64, copy, datetime, html, io, json, math, mimetypes, operator, os, platform, posixpath, queue, shlex
import sys, threading, time, urllib.parse, urllib.request, shutil, subprocess, tempfile, socket
from array import array
from html.parser import HTMLParser

import pygame as pg

W, H, TASK, HOME = 1100, 700, 40, "/home/user"
DISK = os.path.join(os.path.dirname(os.path.abspath(__file__)), "vm_disk.json")
BOOT_TIME = time.time()

C = dict(win=(30, 32, 40), bar=(44, 47, 60), barf=(58, 84, 160), txt=(230, 232, 240),
         dim=(140, 146, 165), acc=(95, 145, 255), btn=(52, 56, 70), red=(225, 85, 85),
         green=(100, 210, 130), yellow=(240, 200, 90), field=(20, 22, 28), line=(60, 64, 80))
F = {}


def load_fonts():
    sans = "segoeui,dejavusans,helveticaneue,helvetica,arial,liberationsans"
    mono = "consolas,dejavusansmono,menlo,liberationmono,couriernew,monospace"
    S = pg.font.SysFont
    F.update(ui=S(sans, 14), small=S(sans, 12), big=S(sans, 22, bold=True), huge=S(sans, 44, bold=True),
             mono=S(mono, 15), p=S(sans, 15), b=S(sans, 15, bold=True),
             h1=S(sans, 28, bold=True), h2=S(sans, 22, bold=True), h3=S(sans, 18, bold=True))


def text(surf, s, font, color, x, y, center=False):
    img = F[font].render(str(s), True, color)
    if center:
        x -= img.get_width() // 2
    surf.blit(img, (x, y))
    return img.get_width()


def lighten(c, n=22):
    return tuple(min(255, v + n) for v in c)


# --------------------------------------------------------------------------- virtual filesystem
class VFSError(Exception):
    pass


class VFS:
    """Tiny in-memory filesystem persisted to JSON. dir: {"t":"d","c":{}}  file: {"t":"f","d":"text"}"""

    def __init__(s, path):
        s.path, s.quiet = path, False
        try:
            with open(path, encoding="utf-8") as f:
                s.root = json.load(f)
        except Exception:
            s.make_default()

    def make_default(s):
        s.root, s.quiet = {"t": "d", "c": {}}, True
        for d in ("Documents", "Desktop", "Downloads"):
            s.mkdir(f"{HOME}/{d}", True)
        s.mkdir("/tmp", True)
        s.write(f"{HOME}/Documents/readme.txt",
                "Welcome to PyVM!\n\nThis is a virtual machine running inside pygame.\n"
                "Everything you save here lives in vm_disk.json.\n\n"
                "Try the terminal: type 'help'.\n")
        s.write(f"{HOME}/Documents/welcome.html",
                "<h1>Hello from the virtual disk</h1><p>This page is a file stored on the VM's disk, "
                "rendered by the PyVM browser.</p><ul><li>Edit it in Notepad</li><li>Reload the browser</li></ul>"
                "<p><a href='vm://home'>Back to the home page</a></p>")
        s.write(f"{HOME}/Desktop/notes.txt", "Double-click files on the desktop to open them.\n")
        s.quiet = False
        s.save()

    def save(s):
        if s.quiet:
            return
        try:
            with open(s.path, "w", encoding="utf-8") as f:
                json.dump(s.root, f)
        except OSError:
            pass

    def norm(s, p, cwd="/"):
        if p == "~" or p.startswith("~/"):
            p = HOME + p[1:]
        return posixpath.normpath(posixpath.join(cwd, p))

    def get(s, p):
        n = s.root
        for part in [x for x in p.split("/") if x]:
            if n["t"] != "d" or part not in n["c"]:
                return None
            n = n["c"][part]
        return n

    def isdir(s, p):
        n = s.get(p)
        return bool(n and n["t"] == "d")

    def isfile(s, p):
        n = s.get(p)
        return bool(n and n["t"] == "f")

    def parent(s, p):
        d, b = posixpath.split(p)
        n = s.get(d)
        if not b:
            raise VFSError("invalid path")
        if not n or n["t"] != "d":
            raise VFSError(f"{d}: no such directory")
        return n, b

    def listdir(s, p):
        n = s.get(p)
        if not n:
            raise VFSError(f"{p}: no such file or directory")
        if n["t"] != "d":
            raise VFSError(f"{p}: not a directory")
        return sorted(n["c"].items(), key=lambda kv: (kv[1]["t"] != "d", kv[0].lower()))

    def read_bytes(s, p):
        n = s.get(p)
        if not n or n["t"] != "f":
            raise VFSError(f"{p}: not a file")
        if n.get("encoding") == "base64":
            return base64.b64decode(n["d"])
        return n["d"].encode("utf-8")

    def write_bytes(s, p, data):
        par, b = s.parent(p)
        if b in par["c"] and par["c"][b]["t"] == "d":
            raise VFSError(f"{p}: is a directory")
        par["c"][b] = {"t": "f", "d": base64.b64encode(data).decode("ascii"), "encoding": "base64"}
        s.save()

    def read(s, p):
        n = s.get(p)
        if not n:
            raise VFSError(f"{p}: no such file")
        if n["t"] == "d":
            raise VFSError(f"{p}: is a directory")
        if n.get("encoding") == "base64":
            try:
                return base64.b64decode(n["d"]).decode("utf-8")
            except UnicodeError:
                raise VFSError(f"{p}: binary file (use Export in Files)")
        return n["d"]

    def write(s, p, data):
        par, b = s.parent(p)
        if b in par["c"] and par["c"][b]["t"] == "d":
            raise VFSError(f"{p}: is a directory")
        par["c"][b] = {"t": "f", "d": data}
        s.save()

    def mkdir(s, p, parents=False):
        n = s.root
        parts = [x for x in p.split("/") if x]
        for i, part in enumerate(parts):
            if part not in n["c"]:
                if i < len(parts) - 1 and not parents:
                    raise VFSError(f"{p}: parent directory missing (use -p)")
                n["c"][part] = {"t": "d", "c": {}}
            elif n["c"][part]["t"] != "d":
                raise VFSError(f"{p}: file exists")
            elif i == len(parts) - 1 and not parents:
                raise VFSError(f"{p}: already exists")
            n = n["c"][part]
        s.save()

    def remove(s, p, recursive=False):
        if p == "/":
            raise VFSError("refusing to remove /")
        n = s.get(p)
        if not n:
            raise VFSError(f"{p}: no such file or directory")
        if n["t"] == "d" and n["c"] and not recursive:
            raise VFSError(f"{p}: directory not empty (use rm -r)")
        par, b = s.parent(p)
        del par["c"][b]
        s.save()

    def _dest(s, src, dst):
        if s.isdir(dst):
            dst = posixpath.join(dst, posixpath.basename(src))
        if s.get(dst):
            raise VFSError(f"{dst}: already exists")
        if dst == src or dst.startswith(src + "/"):
            raise VFSError("cannot move/copy a folder into itself")
        return dst

    def copy(s, src, dst):
        n = s.get(src)
        if not n:
            raise VFSError(f"{src}: no such file or directory")
        dst = s._dest(src, dst)
        par, b = s.parent(dst)
        par["c"][b] = copy.deepcopy(n)
        s.save()

    def move(s, src, dst):
        n = s.get(src)
        if not n or src == "/":
            raise VFSError(f"{src}: no such file or directory")
        dst = s._dest(src, dst)
        par, b = s.parent(dst)
        sp, sb = s.parent(src)
        par["c"][b] = n
        del sp["c"][sb]
        s.save()

    def size(s, n=None):
        n = n or s.root
        return len(base64.b64decode(n["d"])) if n["t"] == "f" and n.get("encoding") == "base64" else (len(n["d"].encode()) if n["t"] == "f" else sum(s.size(c) for c in n["c"].values()))


# --------------------------------------------------------------------------- helpers
OPS = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul, ast.Div: operator.truediv,
       ast.Mod: operator.mod, ast.Pow: operator.pow, ast.FloorDiv: operator.floordiv}
FUNS = dict(sqrt=math.sqrt, sin=math.sin, cos=math.cos, tan=math.tan, log=math.log10, ln=math.log,
            abs=abs, round=round, floor=math.floor, ceil=math.ceil)
CONSTS = dict(pi=math.pi, e=math.e)


def safe_eval(expr):
    def ev(n):
        if isinstance(n, ast.Expression):
            return ev(n.body)
        if isinstance(n, ast.Constant) and isinstance(n.value, (int, float)) and not isinstance(n.value, bool):
            return n.value
        if isinstance(n, ast.BinOp) and type(n.op) in OPS:
            a, b = ev(n.left), ev(n.right)
            if isinstance(n.op, ast.Pow) and abs(b) > 1000:
                raise ValueError("exponent too large")
            return OPS[type(n.op)](a, b)
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, (ast.USub, ast.UAdd)):
            return -ev(n.operand) if isinstance(n.op, ast.USub) else ev(n.operand)
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in FUNS and not n.keywords:
            return FUNS[n.func.id](*[ev(a) for a in n.args])
        if isinstance(n, ast.Name) and n.id in CONSTS:
            return CONSTS[n.id]
        raise ValueError("bad expression")
    return ev(ast.parse(expr.strip().replace("^", "**"), mode="eval"))


def fmt_num(v):
    if isinstance(v, float):
        if v != v or v in (math.inf, -math.inf):
            return "Error"
        if v.is_integer() and abs(v) < 1e15:
            return str(int(v))
        return f"{v:.12g}"
    s = str(v)
    return s if len(s) < 30 else f"{float(v):.12g}"


_beep = None


def beep():
    global _beep
    try:
        if _beep is None:
            if not pg.mixer.get_init():
                pg.mixer.init(22050, -16, 1)
            data = array("h", [int(9000 * math.sin(2 * math.pi * 880 * i / 22050)) for i in range(7000)])
            _beep = pg.mixer.Sound(buffer=data.tobytes())
        _beep.play()
    except Exception:
        pass


class TextField:
    def __init__(s, t=""):
        s.t, s.c = t, len(t)

    def key(s, e):
        if e.type == pg.TEXTINPUT:
            s.t = s.t[:s.c] + e.text + s.t[s.c:]
            s.c += len(e.text)
        elif e.type == pg.KEYDOWN:
            k = e.key
            if k == pg.K_BACKSPACE and s.c:
                s.t = s.t[:s.c - 1] + s.t[s.c:]
                s.c -= 1
            elif k == pg.K_DELETE:
                s.t = s.t[:s.c] + s.t[s.c + 1:]
            elif k == pg.K_LEFT:
                s.c = max(0, s.c - 1)
            elif k == pg.K_RIGHT:
                s.c = min(len(s.t), s.c + 1)
            elif k == pg.K_HOME:
                s.c = 0
            elif k == pg.K_END:
                s.c = len(s.t)
            elif k in (pg.K_RETURN, pg.K_KP_ENTER):
                return "enter"
            elif k == pg.K_ESCAPE:
                return "esc"
        return None

    def draw(s, surf, rect, font="ui", fg=None, bg=None, caret=True):
        rect = pg.Rect(rect)
        pg.draw.rect(surf, bg or C["field"], rect, border_radius=5)
        f = F[font]
        cx = f.size(s.t[:s.c])[0]
        off = max(0, cx - (rect.w - 14))
        old = surf.get_clip()
        surf.set_clip(rect.inflate(-6, 0))
        img = f.render(s.t, True, fg or C["txt"])
        surf.blit(img, (rect.x + 7 - off, rect.y + (rect.h - img.get_height()) // 2))
        if caret and pg.time.get_ticks() // 500 % 2 == 0:
            pg.draw.line(surf, fg or C["txt"], (rect.x + 7 + cx - off, rect.y + 4),
                         (rect.x + 7 + cx - off, rect.bottom - 5))
        surf.set_clip(old)


def draw_file_icon(surf, kind, x, y, s=18):
    if kind == "dir":
        pg.draw.rect(surf, (225, 180, 70), (x, y + 3, s, s - 5), border_radius=3)
        pg.draw.rect(surf, (200, 150, 50), (x, y + 1, s // 2, 4), border_radius=2)
    else:
        pg.draw.rect(surf, (225, 228, 238), (x + 2, y, s - 4, s), border_radius=2)
        pg.draw.line(surf, (150, 155, 175), (x + 5, y + 6), (x + s - 5, y + 6))
        pg.draw.line(surf, (150, 155, 175), (x + 5, y + 10), (x + s - 5, y + 10))


# --------------------------------------------------------------------------- app base
class App:
    title = "App"
    size = (520, 400)
    icon = ("?", (100, 100, 100))

    def __init__(s, vm):
        s.vm, s.btns, s.mouse, s.win = vm, [], (-1, -1), None

    def button(s, surf, rect, label, cb, bg=None, fg=None, font="ui"):
        rect = pg.Rect(rect)
        col = bg or C["btn"]
        pg.draw.rect(surf, lighten(col) if rect.collidepoint(s.mouse) else col, rect, border_radius=6)
        img = F[font].render(label, True, fg or C["txt"])
        surf.blit(img, img.get_rect(center=rect.center))
        s.btns.append((rect, cb))

    def event(s, e, pos):
        if pos is not None:
            s.mouse = pos
        if e.type == pg.MOUSEBUTTONDOWN and e.button == 1:
            for r, cb in reversed(s.btns):
                if r.collidepoint(pos):
                    cb()
                    return True
        return False

    def update(s, dt):
        pass

    def draw(s, surf):
        surf.fill(C["win"])


# --------------------------------------------------------------------------- terminal
class Terminal(App):
    title = "Terminal"
    size = (680, 430)
    icon = (">_", (60, 160, 100))

    def __init__(s, vm):
        super().__init__(vm)
        s.cwd, s.lines, s.f, s.hist, s.hi, s.scroll, s.cols, s.cap = HOME, [], TextField(), [], 0, 0, 80, None
        s.out("PyVM terminal 1.0  -  type 'help' for commands.", C["acc"])

    def prompt(s):
        d = "~" + s.cwd[len(HOME):] if s.cwd.startswith(HOME) else s.cwd
        return f"user@pyvm:{d}$ "

    def out(s, t="", col=None):
        if s.cap is not None:
            s.cap.append(str(t))
            return
        col = col or C["txt"]
        for ln in str(t).split("\n"):
            while len(ln) > s.cols:
                s.lines.append([(ln[:s.cols], col)])
                ln = ln[s.cols:]
            s.lines.append([(ln, col)])
        del s.lines[:-3000]

    def p(s, a):
        return s.vm.vfs.norm(a, s.cwd)

    # ---- command execution
    def run(s, line):
        s.lines.append([(s.prompt(), C["green"]), (line, C["txt"])])
        if not line.strip():
            return
        s.hist.append(line)
        s.hi = len(s.hist)
        try:
            lx = shlex.shlex(line, posix=True, punctuation_chars=">")
            lx.whitespace_split = True
            toks = list(lx)
        except ValueError as e:
            return s.out(f"parse error: {e}", C["red"])
        redir = None
        for i, t in enumerate(toks):
            if t in (">", ">>"):
                if i + 1 >= len(toks):
                    return s.out("syntax error: missing file after redirect", C["red"])
                redir, toks = (t, toks[i + 1]), toks[:i]
                break
        if not toks:
            return
        fn = getattr(s, "c_" + toks[0].replace("-", "_"), None)
        if not fn:
            return s.out(f"{toks[0]}: command not found", C["red"])
        s.cap = [] if redir else None
        try:
            fn(toks[1:])
        except VFSError as e:
            s.cap = None
            s.out(str(e), C["red"])
        except Exception as e:
            s.cap = None
            s.out(f"error: {e}", C["red"])
        if redir:
            data, s.cap = "\n".join(s.cap) + "\n", None
            try:
                path = s.p(redir[1])
                if redir[0] == ">>" and s.vm.vfs.isfile(path):
                    data = s.vm.vfs.read(path) + data
                s.vm.vfs.write(path, data)
            except VFSError as e:
                s.out(str(e), C["red"])

    def c_help(s, a):
        s.out("Commands:\n  ls [-l] [dir]   cd   pwd   mkdir [-p]   touch   cat   rm [-r]   cp   mv   echo\n"
              "  tree   grep [-i] pat file   wc file   head/tail file   clear   date   uptime   whoami\n"
              "  hostname   uname   neofetch   df   history   calc <expr>   edit <file>\n"
              "  open <app|file|dir>   browse <url>   exit\n"
              "Apps: terminal files notepad calculator clock browser music settings task_manager\n"
              "Redirect output with > and >>   e.g.  echo hi > note.txt\n"
              "Keys: Up/Down history, Ctrl+L clear, Ctrl+C cancel, PgUp/PgDn scroll", C["dim"])

    def c_ls(s, a):
        flags = [x for x in a if x.startswith("-")]
        paths = [x for x in a if not x.startswith("-")] or ["."]
        vfs = s.vm.vfs
        for path in paths:
            p = s.p(path)
            ents = vfs.listdir(p) if vfs.isdir(p) else [(posixpath.basename(p), vfs.get(p))]
            if not vfs.get(p):
                raise VFSError(f"{p}: no such file or directory")
            if s.cap is not None:
                for n, _ in ents:
                    s.out(n)
            elif "-l" in flags:
                for n, v in ents:
                    isd = v["t"] == "d"
                    s.lines.append([(f"{'d' if isd else '-'}rw-  {vfs.size(v):>8}  ", C["dim"]),
                                    (n + ("/" if isd else ""), C["acc"] if isd else C["txt"])])
            elif ents:
                names = [n + ("/" if v["t"] == "d" else "") for n, v in ents]
                wd = max(map(len, names)) + 2
                per = max(1, s.cols // wd)
                for i in range(0, len(names), per):
                    s.lines.append([(n.ljust(wd), C["acc"] if n.endswith("/") else C["txt"])
                                    for n in names[i:i + per]])

    def c_cd(s, a):
        p = s.p(a[0] if a else "~")
        if not s.vm.vfs.isdir(p):
            raise VFSError(f"{p}: not a directory")
        s.cwd = p

    def c_pwd(s, a):
        s.out(s.cwd)

    def c_mkdir(s, a):
        for x in [x for x in a if not x.startswith("-")]:
            s.vm.vfs.mkdir(s.p(x), "-p" in a)

    def c_touch(s, a):
        for x in a:
            if not s.vm.vfs.get(s.p(x)):
                s.vm.vfs.write(s.p(x), "")

    def c_cat(s, a):
        if not a:
            raise VFSError("usage: cat <file>")
        for x in a:
            s.out(s.vm.vfs.read(s.p(x)).rstrip("\n"))

    def c_head(s, a):
        s.out("\n".join(s.vm.vfs.read(s.p(a[0])).split("\n")[:10]))

    def c_tail(s, a):
        s.out("\n".join(s.vm.vfs.read(s.p(a[0])).rstrip("\n").split("\n")[-10:]))

    def c_rm(s, a):
        rec = any(x in ("-r", "-rf", "-fr", "-R") for x in a)
        for x in [x for x in a if not x.startswith("-")]:
            s.vm.vfs.remove(s.p(x), rec)

    c_rmdir = c_rm

    def c_cp(s, a):
        a = [x for x in a if not x.startswith("-")]
        if len(a) != 2:
            raise VFSError("usage: cp <src> <dst>")
        s.vm.vfs.copy(s.p(a[0]), s.p(a[1]))

    def c_mv(s, a):
        if len(a) != 2:
            raise VFSError("usage: mv <src> <dst>")
        s.vm.vfs.move(s.p(a[0]), s.p(a[1]))

    def c_echo(s, a):
        s.out(" ".join(a))

    def c_clear(s, a):
        s.lines = []

    def c_date(s, a):
        s.out(datetime.datetime.now().strftime("%a %b %d %H:%M:%S %Y"))

    def c_uptime(s, a):
        t = int(time.time() - BOOT_TIME)
        s.out(f"up {t // 3600}h {t % 3600 // 60}m {t % 60}s")

    def c_whoami(s, a):
        s.out("user")

    def c_hostname(s, a):
        s.out("pyvm")

    def c_uname(s, a):
        s.out(f"PyVM 1.0 pygame-{pg.version.ver} python-{platform.python_version()}")

    def c_df(s, a):
        s.out(f"vdisk: {s.vm.vfs.size()} bytes used (stored in {os.path.basename(DISK)})")

    def c_history(s, a):
        for i, h in enumerate(s.hist):
            s.out(f"{i + 1:>4}  {h}")

    def c_exit(s, a):
        s.vm.close(s.win)

    def c_tree(s, a):
        root = s.p(a[0] if a else ".")
        s.out(root)

        def walk(p, pre, depth):
            ents = s.vm.vfs.listdir(p)
            for i, (n, v) in enumerate(ents):
                last = i == len(ents) - 1
                s.out(f"{pre}{'└── ' if last else '├── '}{n}{'/' if v['t'] == 'd' else ''}")
                if v["t"] == "d" and depth < 6:
                    walk(posixpath.join(p, n), pre + ("    " if last else "│   "), depth + 1)
        walk(root, "", 0)

    def c_grep(s, a):
        ic = "-i" in a
        a = [x for x in a if x != "-i"]
        if len(a) < 2:
            raise VFSError("usage: grep [-i] <pattern> <file>")
        pat = a[0].lower() if ic else a[0]
        for fl in a[1:]:
            for ln in s.vm.vfs.read(s.p(fl)).split("\n"):
                if pat in (ln.lower() if ic else ln):
                    s.out(ln)

    def c_wc(s, a):
        t = s.vm.vfs.read(s.p(a[0]))
        s.out(f"{t.count(chr(10))} lines  {len(t.split())} words  {len(t.encode())} bytes")

    def c_calc(s, a):
        s.out(fmt_num(safe_eval(" ".join(a))))

    def c_edit(s, a):
        s.vm.open("notepad", path=s.p(a[0]) if a else None)

    c_nano = c_edit

    def c_browse(s, a):
        s.vm.open("browser", url=a[0] if a else "vm://home")

    def c_open(s, a):
        if not a:
            raise VFSError("usage: open <app|file|dir>")
        s.vm.open_target(a[0], s.cwd)

    def c_neofetch(s, a):
        art = ["  ____        __     ____  __ ", " |  _ \\ _   _\\ \\   / /  \\/  |", " | |_) | | | |\\ \\ / /| |\\/| |",
               " |  __/| |_| | \\ V / | |  | |", " |_|    \\__, |  \\_/  |_|  |_|", "         |___/                "]
        t = int(time.time() - BOOT_TIME)
        info = ["user@pyvm", "---------", "OS: PyVM 1.0", f"Python: {platform.python_version()}",
                f"pygame: {pg.version.ver}", f"Uptime: {t // 60}m {t % 60}s", f"Windows: {len(s.vm.windows)}",
                f"Disk: {s.vm.vfs.size()} bytes", f"Display: {W}x{H}"]
        for i in range(max(len(art), len(info))):
            s.lines.append([((art[i] if i < len(art) else " " * 31) + "  ", C["acc"]),
                            (info[i] if i < len(info) else "", C["txt"])])

    # ---- events / drawing
    def event(s, e, pos):
        if super().event(e, pos):
            return
        if e.type == pg.MOUSEWHEEL:
            s.scroll += e.y * 3
            return
        if e.type == pg.KEYDOWN:
            k, ctrl = e.key, pg.key.get_mods() & pg.KMOD_CTRL
            if ctrl and k == pg.K_t:
                s.new_tab(); return
            elif ctrl and k == pg.K_w:
                s.close_tab(); return
            elif ctrl and k == pg.K_TAB:
                s.switch_tab((s.tab_index + ( -1 if shift else 1)) % len(s.engines)); return
            if ctrl and k == pg.K_l:
                s.lines = []
                return
            if ctrl and k == pg.K_c:
                s.lines.append([(s.prompt() + s.f.t + "^C", C["dim"])])
                s.f = TextField()
                return
            if k == pg.K_UP and s.hist:
                s.hi = max(0, s.hi - 1)
                s.f = TextField(s.hist[s.hi])
                return
            if k == pg.K_DOWN:
                s.hi = min(len(s.hist), s.hi + 1)
                s.f = TextField(s.hist[s.hi] if s.hi < len(s.hist) else "")
                return
            if k == pg.K_PAGEUP:
                s.scroll += 10
                return
            if k == pg.K_PAGEDOWN:
                s.scroll -= 10
                return
        if s.f.key(e) == "enter":
            line, s.f, s.scroll = s.f.t, TextField(), 0
            s.run(line)

    def draw(s, surf):
        w, h = surf.get_size()
        surf.fill((14, 16, 20))
        mf = F["mono"]
        cw, ch = mf.size("M")[0], mf.get_linesize()
        s.cols, rows = max(20, (w - 12) // cw), max(1, (h - 8) // ch)
        pl = s.prompt()
        allv = s.lines + [[(pl, C["green"]), (s.f.t, C["txt"])]]
        n = len(allv)
        s.scroll = max(0, min(s.scroll, n - rows))
        end = n - s.scroll
        start = max(0, end - rows)
        y = 4
        for ln in allv[start:end]:
            x = 6
            for t, c in ln:
                if t:
                    surf.blit(mf.render(t, True, c), (x, y))
                x += cw * len(t)
            y += ch
        if s.scroll == 0 and pg.time.get_ticks() // 500 % 2 == 0:
            cx = 6 + cw * (len(pl) + s.f.c)
            pg.draw.rect(surf, C["txt"], (cx, 4 + (end - 1 - start) * ch + 1, cw - 1, ch - 2), 1)


# --------------------------------------------------------------------------- calculator
class Calculator(App):
    title = "Calculator"
    size = (320, 440)
    icon = ("#", (230, 120, 60))
    KEYS = [[("C", "C"), ("(", "("), (")", ")"), ("Del", "B")],
            [("sqrt", "sqrt("), ("x^2", "**2"), ("%", "%"), ("/", "/")],
            [("7", "7"), ("8", "8"), ("9", "9"), ("*", "*")],
            [("4", "4"), ("5", "5"), ("6", "6"), ("-", "-")],
            [("1", "1"), ("2", "2"), ("3", "3"), ("+", "+")],
            [("0", "0"), (".", "."), ("Ans", "ANS"), ("=", "=")]]

    def __init__(s, vm):
        super().__init__(vm)
        s.expr, s.ans, s.done, s.hist, s.res_shown = "", "0", False, [], ""

    def press(s, a):
        if a == "C":
            s.expr, s.done = "", False
        elif a == "B":
            s.expr = s.expr[:-1]
            s.done = False
        elif a == "=":
            if not s.expr:
                return
            try:
                r = fmt_num(safe_eval(s.expr))
            except Exception:
                r = "Error"
            s.hist.append(f"{s.expr} = {r}")
            del s.hist[:-3]
            if r != "Error":
                s.ans = r
            s.done, s.res_shown = True, r
        else:
            if a == "ANS":
                a = s.ans
            if s.done:
                s.expr = s.ans + a if a[0] in "+-*/%" else a
                s.done = False
            else:
                s.expr += a

    def preview(s):
        if s.done:
            return s.res_shown
        try:
            return fmt_num(safe_eval(s.expr)) if s.expr else ""
        except Exception:
            return ""

    def event(s, e, pos):
        if super().event(e, pos):
            return
        if e.type == pg.TEXTINPUT:
            for ch in e.text:
                if ch in "0123456789.+-*/%()^":
                    s.press("**" if ch == "^" else ch)
                elif ch == "=":
                    s.press("=")
        elif e.type == pg.KEYDOWN:
            if e.key in (pg.K_RETURN, pg.K_KP_ENTER):
                s.press("=")
            elif e.key == pg.K_BACKSPACE:
                s.press("B")
            elif e.key == pg.K_ESCAPE:
                s.press("C")

    def draw(s, surf):
        w, h = surf.get_size()
        surf.fill(C["win"])
        s.btns = []
        pg.draw.rect(surf, C["field"], (10, 10, w - 20, 110), border_radius=8)
        for i, hline in enumerate(s.hist[-3:]):
            surf.blit(F["small"].render(hline, True, C["dim"]), (w - 20 - F["small"].size(hline)[0], 14 + i * 15))
        ex = s.expr or "0"
        f = F["big"]
        surf.blit(f.render(ex[-26:], True, C["txt"]), (w - 20 - f.size(ex[-26:])[0], 58))
        pv = s.preview()
        if pv:
            col = C["green"] if s.done else C["dim"]
            surf.blit(F["ui"].render("= " + pv, True, col), (w - 20 - F["ui"].size("= " + pv)[0], 92))
        bw, bh, gap = (w - 20 - 3 * 8) // 4, (h - 140 - 5 * 8) // 6, 8
        for r, row in enumerate(s.KEYS):
            for c, (lbl, act) in enumerate(row):
                col = C["acc"] if act == "=" else (C["bar"] if lbl in "C()Del" or lbl in ("sqrt", "x^2", "%", "/", "*", "-", "+") else C["btn"])
                s.button(surf, (10 + c * (bw + gap), 130 + r * (bh + gap), bw, bh), lbl,
                         lambda a=act: s.press(a), bg=col, font="big")


# --------------------------------------------------------------------------- clock
class Clock(App):
    title = "Clock"
    size = (420, 480)
    icon = ("C", (80, 140, 230))

    def __init__(s, vm):
        super().__init__(vm)
        s.tab, s.sw_run, s.sw_t0, s.sw_acc, s.laps = 0, False, 0.0, 0.0, []
        s.tm_set, s.tm_run, s.tm_end, s.tm_left, s.alarm = 300, False, 0.0, 300.0, False

    @property
    def title(s):
        return "Clock - Time's up!" if s.alarm else "Clock"

    def sw_time(s):
        return s.sw_acc + (time.monotonic() - s.sw_t0 if s.sw_run else 0)

    def update(s, dt):
        if s.tm_run:
            s.tm_left = max(0.0, s.tm_end - time.monotonic())
            if s.tm_left <= 0:
                s.tm_run, s.alarm = False, True
                beep()
        if s.alarm and int(time.time() * 2) % 2 == 0 and int(time.time() * 2) != getattr(s, "_lb", 0):
            s._lb = int(time.time() * 2)
            beep()

    def sw_toggle(s):
        if s.sw_run:
            s.sw_acc, s.sw_run = s.sw_time(), False
        else:
            s.sw_t0, s.sw_run = time.monotonic(), True

    def sw_lap(s):
        if s.sw_run:
            s.laps.append(s.sw_time())

    def sw_reset(s):
        s.sw_run, s.sw_acc, s.laps = False, 0.0, []

    def tm_toggle(s):
        if s.alarm:
            return s.tm_reset()
        if s.tm_run:
            s.tm_run = False
        elif s.tm_left > 0:
            s.tm_end, s.tm_run = time.monotonic() + s.tm_left, True

    def tm_reset(s):
        s.tm_run, s.alarm, s.tm_left = False, False, float(s.tm_set)

    def tm_add(s, n):
        if not s.tm_run:
            s.tm_set = max(0, s.tm_set + n)
            s.tm_left, s.alarm = float(s.tm_set), False

    @staticmethod
    def fmt(t, cs=True):
        m, sec = divmod(t, 60)
        return f"{int(m // 60):02d}:{int(m % 60):02d}:{int(sec):02d}" if not cs else f"{int(m):02d}:{int(sec):02d}.{int(t * 100 % 100):02d}"

    def draw(s, surf):
        w, h = surf.get_size()
        surf.fill(C["win"])
        s.btns = []
        for i, n in enumerate(("Clock", "Stopwatch", "Timer")):
            s.button(surf, (10 + i * ((w - 20) // 3), 8, (w - 20) // 3 - 6, 28), n, lambda i=i: setattr(s, "tab", i),
                     bg=C["acc"] if s.tab == i else C["btn"])
        cx = w // 2
        if s.tab == 0:
            now = datetime.datetime.now()
            r = min(w // 2 - 30, (h - 190) // 2)
            cy = 52 + r + 10
            pg.draw.circle(surf, C["field"], (cx, cy), r)
            pg.draw.circle(surf, C["acc"], (cx, cy), r, 3)
            for i in range(60):
                a = math.radians(i * 6)
                l = 10 if i % 5 == 0 else 4
                p1 = (cx + (r - 4) * math.sin(a), cy - (r - 4) * math.cos(a))
                p2 = (cx + (r - 4 - l) * math.sin(a), cy - (r - 4 - l) * math.cos(a))
                pg.draw.line(surf, C["txt"] if i % 5 == 0 else C["dim"], p1, p2, 2 if i % 5 == 0 else 1)
            for i in range(1, 13):
                a = math.radians(i * 30)
                text(surf, i, "ui", C["txt"], cx + (r - 28) * math.sin(a), cy - (r - 28) * math.cos(a) - 8, True)
            sec = now.second + now.microsecond / 1e6
            mn = now.minute + sec / 60
            hr = now.hour % 12 + mn / 60
            for ang, ln, wd, col in ((hr * 30, r * .5, 5, C["txt"]), (mn * 6, r * .75, 3, C["txt"]),
                                     (sec * 6, r * .85, 1, C["red"])):
                a = math.radians(ang)
                pg.draw.line(surf, col, (cx, cy), (cx + ln * math.sin(a), cy - ln * math.cos(a)), wd)
            pg.draw.circle(surf, C["red"], (cx, cy), 5)
            text(surf, now.strftime("%H:%M:%S"), "huge", C["txt"], cx, cy + r + 14, True)
            text(surf, now.strftime("%A, %B %d, %Y"), "ui", C["dim"], cx, cy + r + 66, True)
        elif s.tab == 1:
            text(surf, s.fmt(s.sw_time()), "huge", C["txt"], cx, 70, True)
            bw = (w - 40) // 3
            s.button(surf, (10, 140, bw, 38), "Stop" if s.sw_run else "Start", s.sw_toggle, bg=C["red"] if s.sw_run else C["green"], fg=(10, 10, 10))
            s.button(surf, (20 + bw, 140, bw, 38), "Lap", s.sw_lap)
            s.button(surf, (30 + 2 * bw, 140, bw, 38), "Reset", s.sw_reset)
            for i, lp in enumerate(reversed(s.laps[-9:])):
                n = len(s.laps) - i
                prev = s.laps[n - 2] if n > 1 else 0
                text(surf, f"Lap {n}", "ui", C["dim"], 30, 200 + i * 24)
                text(surf, f"{s.fmt(lp)}   (+{s.fmt(lp - prev)})", "ui", C["txt"], 110, 200 + i * 24)
        else:
            col = C["red"] if s.alarm and int(time.time() * 2) % 2 == 0 else C["txt"]
            text(surf, s.fmt(s.tm_left + (0.99 if s.tm_run else 0), False), "huge", col, cx, 70, True)
            if s.alarm:
                text(surf, "Time's up!", "big", C["red"], cx, 125, True)
            bw = (w - 40) // 3
            for i, (lbl, n) in enumerate((("+1 min", 60), ("+10 sec", 10), ("-1 min", -60))):
                s.button(surf, (10 + i * (bw + 10), 170, bw, 36), lbl, lambda n=n: s.tm_add(n))
            s.button(surf, (10, 220, (w - 30) // 2, 40), "Pause" if s.tm_run else ("Dismiss" if s.alarm else "Start"),
                     s.tm_toggle, bg=C["green"], fg=(10, 10, 10))
            s.button(surf, (20 + (w - 30) // 2, 220, (w - 30) // 2, 40), "Reset", s.tm_reset)
            text(surf, "Tip: set the time with the buttons, then Start", "small", C["dim"], cx, 275, True)


# --------------------------------------------------------------------------- notepad
class Notepad(App):
    size = (640, 460)
    icon = ("N", (225, 175, 55))

    def __init__(s, vm, path=None):
        super().__init__(vm)
        s.path, s.lines, s.r, s.c, s.top, s.hx, s.mod = path, [""], 0, 0, 0, 0, False
        s.prompt, s.msg, s.rows, s.vw = None, "", 10, 300
        if path:
            try:
                s.lines = vm.vfs.read(path).split("\n")
            except VFSError as e:
                s.msg = str(e)

    @property
    def title(s):
        return "Notepad - " + (posixpath.basename(s.path) if s.path else "Untitled") + ("*" if s.mod else "")

    def new(s):
        s.path, s.lines, s.r, s.c, s.mod, s.top, s.hx = None, [""], 0, 0, False, 0, 0

    def save(s):
        if not s.path:
            s.prompt = TextField(HOME + "/Documents/untitled.txt")
            return
        try:
            s.vm.vfs.write(s.path, "\n".join(s.lines))
            s.mod, s.msg = False, "Saved " + s.path
        except VFSError as e:
            s.msg = str(e)

    def ensure(s):
        cw = F["mono"].size("M")[0]
        if s.r < s.top:
            s.top = s.r
        elif s.r >= s.top + s.rows:
            s.top = s.r - s.rows + 1
        cx = s.c * cw
        if cx < s.hx:
            s.hx = cx
        elif cx > s.hx + s.vw:
            s.hx = cx - s.vw

    def insert(s, t):
        ln = s.lines[s.r]
        s.lines[s.r] = ln[:s.c] + t + ln[s.c:]
        s.c += len(t)
        s.mod = True

    def event(s, e, pos):
        if super().event(e, pos):
            return
        if s.prompt:
            r = s.prompt.key(e)
            if r == "esc":
                s.prompt = None
            elif r == "enter":
                s.path, s.prompt = s.vm.vfs.norm(s.prompt.t, HOME), None
                s.save()
            return
        cw, ch = F["mono"].size("M")[0], F["mono"].get_linesize()
        if e.type == pg.MOUSEWHEEL:
            s.top = max(0, min(len(s.lines) - 1, s.top - e.y * 3))
        elif e.type == pg.MOUSEBUTTONDOWN and e.button == 1 and pos[1] > 30:
            s.r = max(0, min(len(s.lines) - 1, s.top + (pos[1] - 30) // ch))
            s.c = max(0, min(len(s.lines[s.r]), round((pos[0] - 50 + s.hx) / cw)))
        elif e.type == pg.TEXTINPUT:
            s.insert(e.text)
        elif e.type == pg.KEYDOWN:
            k, L = e.key, s.lines
            if pg.key.get_mods() & pg.KMOD_CTRL:
                if k == pg.K_s:
                    s.save()
                return
            if k in (pg.K_RETURN, pg.K_KP_ENTER):
                rest = L[s.r][s.c:]
                L[s.r] = L[s.r][:s.c]
                L.insert(s.r + 1, rest)
                s.r, s.c, s.mod = s.r + 1, 0, True
            elif k == pg.K_BACKSPACE:
                if s.c:
                    L[s.r] = L[s.r][:s.c - 1] + L[s.r][s.c:]
                    s.c -= 1
                elif s.r:
                    s.c = len(L[s.r - 1])
                    L[s.r - 1] += L.pop(s.r)
                    s.r -= 1
                s.mod = True
            elif k == pg.K_DELETE:
                if s.c < len(L[s.r]):
                    L[s.r] = L[s.r][:s.c] + L[s.r][s.c + 1:]
                elif s.r < len(L) - 1:
                    L[s.r] += L.pop(s.r + 1)
                s.mod = True
            elif k == pg.K_TAB:
                s.insert("    ")
            elif k == pg.K_LEFT:
                if s.c:
                    s.c -= 1
                elif s.r:
                    s.r -= 1
                    s.c = len(L[s.r])
            elif k == pg.K_RIGHT:
                if s.c < len(L[s.r]):
                    s.c += 1
                elif s.r < len(L) - 1:
                    s.r, s.c = s.r + 1, 0
            elif k == pg.K_UP:
                s.r = max(0, s.r - 1)
            elif k == pg.K_DOWN:
                s.r = min(len(L) - 1, s.r + 1)
            elif k == pg.K_PAGEUP:
                s.r = max(0, s.r - s.rows)
            elif k == pg.K_PAGEDOWN:
                s.r = min(len(L) - 1, s.r + s.rows)
            elif k == pg.K_HOME:
                s.c = 0
            elif k == pg.K_END:
                s.c = len(L[s.r])
            s.c = min(s.c, len(L[s.r]))
        s.ensure()

    def draw(s, surf):
        w, h = surf.get_size()
        surf.fill((22, 24, 30))
        s.btns = []
        pg.draw.rect(surf, C["win"], (0, 0, w, 30))
        s.button(surf, (6, 3, 50, 24), "New", s.new)
        s.button(surf, (62, 3, 50, 24), "Save", s.save)
        text(surf, s.msg[:60], "small", C["dim"], 122, 8)
        mf = F["mono"]
        cw, ch = mf.size("M")[0], mf.get_linesize()
        s.rows, s.vw = max(1, (h - 30 - 24) // ch), w - 60
        ed = pg.Rect(44, 30, w - 44, h - 54)
        pg.draw.rect(surf, C["win"], (0, 30, 44, h - 54))
        old = surf.get_clip()
        surf.set_clip(ed)
        for i in range(s.rows):
            n = s.top + i
            if n >= len(s.lines):
                break
            y = 30 + i * ch
            if n == s.r:
                pg.draw.rect(surf, (32, 35, 45), (44, y, w, ch))
            surf.blit(mf.render(s.lines[n], True, C["txt"]), (50 - s.hx, y))
        if pg.time.get_ticks() // 500 % 2 == 0 and s.top <= s.r < s.top + s.rows:
            x = 50 - s.hx + s.c * cw
            pg.draw.line(surf, C["txt"], (x, 30 + (s.r - s.top) * ch), (x, 30 + (s.r - s.top + 1) * ch - 1))
        surf.set_clip(old)
        for i in range(s.rows):
            if s.top + i < len(s.lines):
                text(surf, s.top + i + 1, "small", C["dim"], 38 - F["small"].size(str(s.top + i + 1))[0], 32 + i * ch)
        pg.draw.rect(surf, C["win"], (0, h - 24, w, 24))
        if s.prompt:
            text(surf, "Save as:", "ui", C["txt"], 8, h - 20)
            s.prompt.draw(surf, (70, h - 22, w - 80, 20))
        else:
            text(surf, f"Ln {s.r + 1}, Col {s.c + 1}   |   Ctrl+S to save", "small", C["dim"], 8, h - 19)


# --------------------------------------------------------------------------- file explorer
class Files(App):
    size = (680, 460)
    icon = ("F", (225, 170, 60))

    def __init__(s, vm, path=HOME, picker=None):
        super().__init__(vm)
        s.picker = picker
        s.path, s.sel, s.scroll, s.prompt, s.status, s.confirm, s.last = path, None, 0, None, "", None, (0, None)
        s.ents = []

    @property
    def title(s):
        return "Files - " + s.path

    def cd(s, p):
        if s.vm.vfs.isdir(p):
            s.path, s.sel, s.scroll, s.status, s.confirm = p, None, 0, "", None

    def up(s):
        s.cd(posixpath.dirname(s.path.rstrip("/")) or "/")

    def join(s, n):
        return posixpath.join(s.path, n)

    def ask(s, kind):
        if kind == "rename":
            if not s.sel:
                s.status = "Select something to rename first"
                return
            s.prompt = (kind, TextField(s.sel))
        else:
            s.prompt = (kind, TextField("new_folder" if kind == "mkdir" else "new_file.txt"))

    def delete(s):
        if not s.sel:
            s.status = "Select something to delete first"
        elif s.confirm != s.sel:
            s.confirm, s.status = s.sel, f"Click Delete again to remove '{s.sel}'"
        else:
            try:
                s.vm.vfs.remove(s.join(s.sel), True)
                s.status = f"Deleted {s.sel}"
            except VFSError as e:
                s.status = str(e)
            s.sel = s.confirm = None

    def open_sel(s, name):
        p = s.join(name)
        if s.vm.vfs.isdir(p):
            s.cd(p)
        else:
            if s.picker:
                if p.lower().endswith((".mp3", ".wav", ".ogg")):
                    s.picker(p)
                    s.vm.close(s.win)
                else:
                    s.status = "Select an MP3, WAV or OGG file"
            else:
                s.vm.open_target(p)

    def commit(s):
        kind, f = s.prompt
        s.prompt = None
        try:
            if kind == "mkdir":
                s.vm.vfs.mkdir(s.join(f.t))
            elif kind == "mkfile":
                if s.vm.vfs.get(s.join(f.t)):
                    raise VFSError("already exists")
                s.vm.vfs.write(s.join(f.t), "")
            else:
                s.vm.vfs.move(s.join(s.sel), s.join(f.t))
            s.sel, s.status = f.t, "Done"
        except VFSError as e:
            s.status = str(e)

    def import_file(s):
        try:
            from tkinter import Tk, filedialog
            root = Tk(); root.withdraw(); root.attributes("-topmost", True)
            src = filedialog.askopenfilename(parent=root)
            root.destroy()
            if src:
                with open(src, "rb") as f:
                    s.vm.vfs.write_bytes(s.join(os.path.basename(src)), f.read())
                s.status = "Imported " + os.path.basename(src)
        except Exception as e:
            s.status = "Import failed: " + str(e)

    def export_file(s):
        if not s.sel or not s.vm.vfs.isfile(s.join(s.sel)):
            s.status = "Select a file first"; return
        try:
            from tkinter import Tk, filedialog
            root = Tk(); root.withdraw(); root.attributes("-topmost", True)
            dst = filedialog.asksaveasfilename(parent=root, initialfile=s.sel)
            root.destroy()
            if dst:
                with open(dst, "wb") as f:
                    f.write(s.vm.vfs.read_bytes(s.join(s.sel)))
                s.status = "Exported to " + dst
        except Exception as e:
            s.status = "Export failed: " + str(e)

    def event(s, e, pos):
        if super().event(e, pos):
            return
        if s.prompt:
            r = s.prompt[1].key(e)
            if r == "esc":
                s.prompt = None
            elif r == "enter":
                s.commit()
            return
        names = [n for n, _ in s.ents]
        if e.type == pg.MOUSEWHEEL:
            s.scroll = max(0, s.scroll - e.y * 2)
        elif e.type == pg.MOUSEBUTTONDOWN and e.button == 1:
            x, y = pos
            if x > 130 and y > 90:
                i = s.scroll + (y - 90) // 24
                if i < len(names):
                    now = pg.time.get_ticks()
                    if s.last[1] == names[i] and now - s.last[0] < 450:
                        s.open_sel(names[i])
                    else:
                        s.sel, s.confirm = names[i], None
                    s.last = (now, names[i])
                else:
                    s.sel = None
        elif e.type == pg.KEYDOWN:
            k = e.key
            i = names.index(s.sel) if s.sel in names else -1
            if k == pg.K_DOWN and names:
                s.sel = names[min(len(names) - 1, i + 1)]
            elif k == pg.K_UP and names:
                s.sel = names[max(0, i - 1)]
            elif k in (pg.K_RETURN, pg.K_KP_ENTER) and s.sel:
                s.open_sel(s.sel)
            elif k == pg.K_BACKSPACE:
                s.up()
            elif k == pg.K_DELETE:
                s.delete()
            elif k == pg.K_F2:
                s.ask("rename")

    def draw(s, surf):
        w, h = surf.get_size()
        surf.fill(C["win"])
        s.btns = []
        x = 6
        for lbl, cb in (("Up", s.up), ("New Folder", lambda: s.ask("mkdir")), ("New File", lambda: s.ask("mkfile")),
                        ("Rename", lambda: s.ask("rename")), ("Delete", s.delete), ("Import", s.import_file), ("Export", s.export_file)):
            bw = F["ui"].size(lbl)[0] + 20
            s.button(surf, (x, 5, bw, 26), lbl, cb, bg=C["red"] if lbl == "Delete" and s.confirm else None)
            x += bw + 6
        pg.draw.rect(surf, C["field"], (6, 40, w - 12, 24), border_radius=5)
        text(surf, s.path, "ui", C["txt"], 14, 44)
        # sidebar
        pg.draw.rect(surf, (24, 26, 33), (0, 70, 128, h - 70))
        text(surf, "PLACES", "small", C["dim"], 12, 76)
        for i, (n, p) in enumerate((("Home", HOME), ("Documents", HOME + "/Documents"), ("Desktop", HOME + "/Desktop"),
                                    ("Downloads", HOME + "/Downloads"), ("Root /", "/"), ("tmp", "/tmp"))):
            r = pg.Rect(6, 96 + i * 28, 116, 24)
            s.button(surf, r, n, lambda p=p: s.cd(p), bg=C["acc"] if s.path == p else (24, 26, 33))
        # list
        try:
            s.ents = s.vm.vfs.listdir(s.path)
        except VFSError:
            s.path, s.ents = "/", s.vm.vfs.listdir("/")
        pg.draw.rect(surf, C["bar"], (130, 70, w - 130, 20))
        text(surf, "Name", "small", C["dim"], 170, 73)
        text(surf, "Size", "small", C["dim"], w - 90, 73)
        vis = max(1, (h - 90 - 28) // 24)
        s.scroll = max(0, min(s.scroll, max(0, len(s.ents) - vis)))
        for i, (n, v) in enumerate(s.ents[s.scroll:s.scroll + vis]):
            y = 90 + i * 24
            if n == s.sel:
                pg.draw.rect(surf, (55, 80, 150), (130, y, w - 130, 24))
            draw_file_icon(surf, "dir" if v["t"] == "d" else "file", 140, y + 3)
            text(surf, n, "ui", C["txt"], 166, y + 4)
            text(surf, "" if v["t"] == "d" else f"{s.vm.vfs.size(v)} B", "small", C["dim"], w - 90, y + 6)
        if not s.ents:
            text(surf, "(empty folder)", "ui", C["dim"], 150, 100)
        pg.draw.rect(surf, C["bar"], (0, h - 28, w, 28))
        if s.prompt:
            lbl = {"mkdir": "New folder:", "mkfile": "New file:", "rename": "Rename to:"}[s.prompt[0]]
            text(surf, lbl, "ui", C["txt"], 8, h - 22)
            s.prompt[1].draw(surf, (100, h - 25, w - 110, 22))
        else:
            text(surf, s.status or f"{len(s.ents)} items", "small", C["dim"], 10, h - 21)


# --------------------------------------------------------------------------- browser
HOME_HTML = """<h1>PyVM Browser</h1>
<p>A small text browser: it renders headings, paragraphs, lists and links. It does <b>not</b> run JavaScript or load images.</p>
<h2>Try these</h2>
<ul>
<li><a href="https://example.com">example.com</a></li>
<li><a href="https://en.wikipedia.org/wiki/Python_(programming_language)">Wikipedia: Python</a></li>
<li><a href="https://html.duckduckgo.com/html/?q=pygame">Search for "pygame"</a></li>
<li><a href="vm:///home/user/Documents/welcome.html">A page stored on the virtual disk</a></li>
</ul>
<p>Type a URL or search words into the address bar above.</p>"""


class Parser(HTMLParser):
    SKIP = {"script", "style", "noscript", "svg", "template", "iframe"}
    BLOCK = {"p", "div", "section", "article", "header", "footer", "nav", "main", "ul", "ol", "table", "tr", "form",
             "blockquote", "pre", "figure", "aside", "dl", "dt", "dd", "fieldset", "body", "html", "center"}

    def __init__(s):
        super().__init__(convert_charrefs=True)
        s.tok, s.title, s.skip, s.in_title, s.href, s.lvl, s.bold = [], "", 0, False, None, 0, False

    def handle_starttag(s, tag, attrs):
        a = dict(attrs)
        if tag == "title":
            s.in_title = True
        elif tag in s.SKIP:
            s.skip += 1
        elif tag in s.BLOCK:
            s.tok.append(("nl", 8))
        elif tag in ("h1", "h2", "h3", "h4", "h5", "h6"):
            s.tok.append(("nl", 12))
            s.lvl = min(3, int(tag[1]))
        elif tag == "br":
            s.tok.append(("nl", 0))
        elif tag == "li":
            s.tok += [("nl", 2), ("w", "•", None, 0, False)]
        elif tag == "hr":
            s.tok += [("nl", 6), ("hr",), ("nl", 6)]
        elif tag == "a":
            s.href = a.get("href")
        elif tag in ("b", "strong"):
            s.bold = True
        elif tag == "img" and a.get("alt"):
            s.tok.append(("w", f"[img: {a['alt'][:30]}]", None, 0, False))

    def handle_endtag(s, tag):
        if tag == "title":
            s.in_title = False
        elif tag in s.SKIP:
            s.skip = max(0, s.skip - 1)
        elif tag in s.BLOCK:
            s.tok.append(("nl", 8))
        elif tag in ("h1", "h2", "h3", "h4", "h5", "h6"):
            s.tok.append(("nl", 12))
            s.lvl = 0
        elif tag == "li":
            s.tok.append(("nl", 0))
        elif tag == "a":
            s.href = None
        elif tag in ("b", "strong"):
            s.bold = False

    def handle_data(s, d):
        if s.in_title:
            s.title += d
        elif not s.skip and len(s.tok) < 30000:
            for w in d.split():
                s.tok.append(("w", w, s.href, s.lvl, s.bold))


def parse_html(src):
    p = Parser()
    try:
        p.feed(src)
        p.close()
    except Exception:
        pass
    return p.tok, p.title.strip()


def parse_text(src):
    tok = []
    for ln in src.split("\n")[:5000]:
        tok += [("w", w, None, 0, False) for w in ln.split()]
        tok.append(("nl", 0 if ln.strip() else 8))
    return tok, ""


def norm_url(t):
    t = t.strip()
    if "://" in t or t.startswith("vm:"):
        return t
    if " " not in t and "." in t:
        return "https://" + t
    return "https://html.duckduckgo.com/html/?q=" + urllib.parse.quote_plus(t)


def resolve_link(base, href):
    q = urllib.parse.urlparse(href).query
    if "uddg=" in href:
        return urllib.parse.parse_qs(q).get("uddg", [href])[0]
    if base.startswith("vm://"):
        return href if "://" in href else "vm://" + posixpath.normpath(posixpath.join(posixpath.dirname(base[5:]), href))
    return urllib.parse.urljoin(base, href)


class BasicBrowser(App):
    size = (820, 560)
    icon = ("W", (70, 150, 220))

    def __init__(s, vm, url="vm://home"):
        super().__init__(vm)
        s.field, s.hist, s.hi, s.gen, s.result = TextField(), [], -1, 0, None
        s.tokens, s.cur, s.ptitle, s.loading, s.scroll, s.links, s.lkey, s.items, s.height, s.hover = \
            [], "", "", False, 0, [], None, [], 0, None
        s.go(url)

    @property
    def title(s):
        return "Browser - " + (s.ptitle or s.cur or "New tab")[:50]

    def go(s, url, push=True):
        url = norm_url(url)
        s.gen += 1
        s.loading = True
        s.field = TextField(url)
        if push:
            s.hist = s.hist[:s.hi + 1] + [url]
            s.hi = len(s.hist) - 1
        threading.Thread(target=s._load, args=(s.gen, url), daemon=True).start()

    def back(s):
        if s.hi > 0:
            s.hi -= 1
            s.go(s.hist[s.hi], False)

    def fwd(s):
        if s.hi < len(s.hist) - 1:
            s.hi += 1
            s.go(s.hist[s.hi], False)

    def _load(s, g, url):
        try:
            if url.startswith("vm://"):
                p = url[5:]
                if p.startswith("/"):
                    src, ctype = s.vm.vfs.read(p), "text/html" if p.endswith((".html", ".htm")) else "text/plain"
                else:
                    src, ctype = HOME_HTML, "text/html"
                final = url
            else:
                req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (PyVM Browser)"})
                with urllib.request.urlopen(req, timeout=12) as r:
                    raw, ctype, final = r.read(2_000_000), r.headers.get("Content-Type", ""), r.geturl()
                    cs = r.headers.get_content_charset() or "utf-8"
                try:
                    src = raw.decode(cs, "replace")
                except LookupError:
                    src = raw.decode("utf-8", "replace")
            is_html = "html" in ctype or src.lstrip()[:15].lower().startswith(("<!doctype", "<html"))
            tok, title = parse_html(src) if is_html else parse_text(src)
            s.result = (g, final, tok, title)
        except Exception as e:
            s.result = (g, url, [("w", "Could not load page:", None, 3, True), ("nl", 8), ("w", str(e), None, 0, False)], "Error")

    def update(s, dt):
        if s.result:
            g, final, tok, title = s.result
            s.result = None
            if g == s.gen:
                s.tokens, s.cur, s.ptitle, s.loading, s.scroll, s.lkey = tok, final, title, False, 0, None
                s.field = TextField(final)

    def layout(s, width):
        items, links, x, y, lh, gapped, pad = [], [], 0, 10, 0, True, 14
        maxw = width - 2 * pad - 10

        def nl(gap=0):
            nonlocal x, y, lh, gapped
            if x > 0:
                y, x, lh = y + lh + 3, 0, 0
            if gap and not gapped:
                y += gap
                gapped = True
        for t in s.tokens:
            if t[0] == "nl":
                nl(t[1])
            elif t[0] == "hr":
                nl()
                items.append((pad, y, None, None, None, None))
                gapped = False
            else:
                _, word, href, lvl, bold = t
                f = F["h%d" % lvl] if lvl else F["b" if bold else "p"]
                ww = f.size(word)[0]
                if x > 0 and x + ww > maxw:
                    nl()
                col = C["acc"] if href else ((255, 255, 255) if lvl else (215, 218, 228))
                items.append((pad + x, y, word, f, col, href))
                if href:
                    links.append((pg.Rect(pad + x, y, ww, f.get_height()), href))
                x += ww + f.size(" ")[0]
                lh, gapped = max(lh, f.get_height()), False
        s.items, s.links, s.height, s.lkey = items, links, y + lh + 20, width

    def event(s, e, pos):
        if super().event(e, pos):
            return
        if e.type == pg.MOUSEWHEEL:
            s.scroll -= e.y * 50
        elif e.type == pg.MOUSEMOTION:
            s.hover = next((h for r, h in s.links if r.collidepoint(pos[0], pos[1] - 40 + s.scroll)), None) if pos[1] > 40 else None
        elif e.type == pg.MOUSEBUTTONDOWN and e.button == 1 and pos[1] > 40:
            for r, href in s.links:
                if r.collidepoint(pos[0], pos[1] - 40 + s.scroll):
                    if not href.startswith(("#", "javascript:", "mailto:")):
                        s.go(resolve_link(s.cur, href))
                    return
        elif e.type == pg.KEYDOWN and e.key in (pg.K_PAGEDOWN, pg.K_PAGEUP):
            s.scroll += 400 if e.key == pg.K_PAGEDOWN else -400
        elif e.type == pg.KEYDOWN and e.key in (pg.K_UP, pg.K_DOWN):
            s.scroll += 40 if e.key == pg.K_DOWN else -40
        elif s.field.key(e) == "enter":
            s.go(s.field.t)

    def draw(s, surf):
        w, h = surf.get_size()
        surf.fill((24, 26, 32))
        s.btns = []
        if s.lkey != w:
            s.layout(w)
        view = h - 40 - 20
        s.scroll = max(0, min(s.scroll, max(0, s.height - view)))
        old = surf.get_clip()
        surf.set_clip((0, 40, w, view))
        for x, y, word, f, col, href in s.items:
            ry = 40 + y - s.scroll
            if ry < 20 or ry > h:
                continue
            if word is None:
                pg.draw.line(surf, C["line"], (x, ry), (w - 24, ry))
                continue
            surf.blit(f.render(word, True, col), (x, ry))
            if href:
                pg.draw.line(surf, col, (x, ry + f.get_height() - 2), (x + f.size(word)[0], ry + f.get_height() - 2))
        surf.set_clip(old)
        if s.height > view:
            th = max(24, view * view // s.height)
            ty = 40 + (view - th) * s.scroll // max(1, s.height - view)
            pg.draw.rect(surf, C["line"], (w - 8, ty, 5, th), border_radius=3)
        pg.draw.rect(surf, C["bar"], (0, 0, w, 28))
        for i, engine in enumerate(s.engines[:max(1, (w - 45) // 135)]):
            r = pg.Rect(i * 135, 2, 132, 24)
            pg.draw.rect(surf, C["barf"] if i == s.tab_index else C["btn"], r, border_radius=5)
            text(surf, (engine.title or "New tab")[:15], "small", C["txt"], r.x + 7, r.y + 4)
        s.button(surf, (min(len(s.engines) * 135, w - 42), 2, 34, 24), "+", s.new_tab)
        pg.draw.rect(surf, C["win"], (0, 28, w, 40))
        for i, (lbl, cb) in enumerate((("<", s.back), (">", s.fwd), ("R", lambda: s.go(s.cur or s.field.t, False)),
                                       ("H", lambda: s.go("vm://home")))):
            s.button(surf, (6 + i * 32, 34, 28, 28), lbl, cb)
        s.field.draw(surf, (140, 6, w - 148, 28))
        pg.draw.rect(surf, C["win"], (0, h - 20, w, 20))
        text(surf, "Loading..." if s.loading else (s.hover or s.cur)[:110], "small", C["dim"], 8, h - 17)


# --------------------------------------------------------------------------- real browser (Chromium via Playwright)
HOME_URL = "http://vm.local/__home"
BOOKMARKS = HOME + "/.bookmarks.json"
PROFILE_DIR = os.path.join(os.path.dirname(DISK), "vm_browser_profile")
CLIP = [""]
SITES = [("Wikipedia", "https://www.wikipedia.org"), ("DuckDuckGo", "https://duckduckgo.com"),
         ("YouTube", "https://www.youtube.com"), ("GitHub", "https://github.com"),
         ("Reddit", "https://www.reddit.com"), ("Hacker News", "https://news.ycombinator.com"),
         ("Python", "https://www.python.org"), ("Weather", "https://wttr.in"),
         ("Disk page", "http://vm.local/home/user/Documents/welcome.html")]
HOME_TPL = """<!doctype html><html><head><meta charset=utf-8><title>New Tab</title><style>
body{margin:0;font-family:system-ui,Segoe UI,Arial,sans-serif;background:linear-gradient(160deg,#141a33,#1f2f5f);color:#e8ebf5;min-height:100vh}
.w{max-width:760px;margin:0 auto;padding:7vh 20px}h1{font-weight:600;font-size:34px;margin:0 0 22px;text-align:center}
form{display:flex;margin-bottom:30px}input{flex:1;padding:14px 20px;border-radius:26px;border:0;font-size:17px;outline:0;background:#fff;color:#111}
h2{font-size:12px;letter-spacing:.14em;text-transform:uppercase;color:#9aa6cc;margin:26px 0 10px}
.g{display:grid;grid-template-columns:repeat(auto-fill,minmax(125px,1fr));gap:12px}
a.t{display:block;padding:16px 8px;text-align:center;border-radius:12px;background:rgba(255,255,255,.08);color:#fff;text-decoration:none;transition:.15s;font-size:14px;overflow:hidden;white-space:nowrap;text-overflow:ellipsis}
a.t:hover{background:rgba(255,255,255,.2);transform:translateY(-2px)}
.i{width:44px;height:44px;border-radius:50%;margin:0 auto 8px;display:flex;align-items:center;justify-content:center;font-weight:700;font-size:20px}
</style></head><body><div class=w><h1>PyVM Browser</h1>
<form action="https://duckduckgo.com/" method="get"><input name=q autofocus autocomplete=off placeholder="Search the web..."></form>
<h2>Quick links</h2><div class=g>%%TILES%%</div>%%BM%%</div></body></html>"""
ERR_TPL = ("<body style='font-family:sans-serif;background:#1d2030;color:#e8ebf5;padding:60px'>"
           "<h2>This page can't be reached</h2><p>%s</p><p style='color:#9aa6cc'>Check the address or your internet connection.</p></body>")
INIT_JS = """(()=>{if(window.top!==window)return;window.open=function(u){if(u){location.href=u}return null};
document.addEventListener('click',function(e){var a=e.target&&e.target.closest?e.target.closest('a[target]'):null;
if(a&&a.target&&['_self','_top','_parent'].indexOf(a.target)<0){a.target='_self'}},true)})();"""
KEYMAP = {pg.K_RETURN: "Enter", pg.K_KP_ENTER: "Enter", pg.K_BACKSPACE: "Backspace", pg.K_TAB: "Tab",
          pg.K_ESCAPE: "Escape", pg.K_UP: "ArrowUp", pg.K_DOWN: "ArrowDown", pg.K_LEFT: "ArrowLeft",
          pg.K_RIGHT: "ArrowRight", pg.K_HOME: "Home", pg.K_END: "End", pg.K_PAGEUP: "PageUp",
          pg.K_PAGEDOWN: "PageDown", pg.K_DELETE: "Delete"}


def put_clip(t):
    CLIP[0] = t
    try:
        pg.scrap.put_text(t)
    except Exception:
        pass


def get_clip():
    try:
        return pg.scrap.get_text() or CLIP[0]
    except Exception:
        return CLIP[0]


def get_bookmarks(vfs):
    try:
        return [tuple(b) for b in json.loads(vfs.read(BOOKMARKS))]
    except Exception:
        return []


def home_html(vfs):
    def tile(name, url):
        hue = sum(map(ord, name)) * 37 % 360
        return (f"<a class=t href='{html.escape(url, True)}'><div class=i style='background:hsl({hue},55%,42%)'>"
                f"{html.escape(name[:1].upper())}</div>{html.escape(name)}</a>")
    bm = get_bookmarks(vfs)
    bms = "<h2>Bookmarks</h2><div class=g>" + "".join(tile(t or u, u) for t, u in bm) + "</div>" if bm else ""
    return HOME_TPL.replace("%%TILES%%", "".join(tile(n, u) for n, u in SITES)).replace("%%BM%%", bms)


def to_real(url):
    if url == "vm://home":
        return HOME_URL
    return "http://vm.local/" + url[5:].lstrip("/") if url.startswith("vm://") else url


def to_display(url):
    if url == HOME_URL:
        return "vm://home"
    return "vm:///" + url[len("http://vm.local/"):] if url.startswith("http://vm.local/") else url


def norm_live(t):
    t = t.strip()
    if t.startswith("vm:"):
        return to_real(t)
    if "://" in t or t.startswith("about:"):
        return t
    if " " not in t and ("." in t or t.startswith("localhost")):
        return "https://" + t
    return "https://duckduckgo.com/?q=" + urllib.parse.quote_plus(t)


class WebEngine(threading.Thread):
    """Runs headless Chromium (Playwright) in its own thread. The GUI sends commands and reads JPEG frames."""
    UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
          "Chrome/131.0.0.0 Safari/537.36")
    profile_busy = False

    def __init__(s, vfs, w, h, config=None):
        super().__init__(daemon=True)
        s.config = config or {}
        s.vfs, s.vp, s.q, s.alive = vfs, (w, h), queue.Queue(), True
        s.frame, s.fid, s.url, s.title, s.loading, s.error = None, 0, "", "", True, None
        s.status, s.status_t, s.ack, s.last_frame, s.clip, s.clip_id = "", 0.0, None, 0.0, "", 0

    def cmd(s, *c):
        s.q.put(c)

    def stop(s):
        s.alive = False

    def say(s, t):
        s.status, s.status_t = t, time.time()

    def run(s):
        own = False
        try:
            from playwright.sync_api import sync_playwright
        except ImportError:
            s.error = "playwright"
            return
        try:
            with sync_playwright() as p:
                args = ["--disable-blink-features=AutomationControlled", "--autoplay-policy=no-user-gesture-required",
                        "--disable-background-media-suspend", "--disable-renderer-backgrounding",
                        "--disable-background-timer-throttling"]
                # A visible (headed) Chromium process can use the host audio output.
                # It is positioned away from the PyVM desktop; headless mode is the fallback.
                headed = bool(s.config.get("browser_audio", True)) and bool(os.environ.get("DISPLAY") or os.environ.get("WAYLAND_DISPLAY") or sys.platform in ("win32", "darwin"))
                if headed:
                    args += ["--window-position=-16000,-16000", "--window-size=960,720"]
                opts = dict(viewport={"width": s.vp[0], "height": s.vp[1]}, user_agent=s.UA, locale="en-US")
                ctx = None
                if not WebEngine.profile_busy:
                    WebEngine.profile_busy = own = True
                    try:
                        ctx = p.chromium.launch_persistent_context(PROFILE_DIR, headless=not headed, accept_downloads=True, args=args, **opts)
                    except Exception:
                        WebEngine.profile_busy = own = False
                if ctx is None:
                    try:
                        ctx = p.chromium.launch(headless=not headed, args=args).new_context(accept_downloads=True, **opts)
                    except Exception:
                        ctx = p.chromium.launch(headless=True, args=args).new_context(accept_downloads=True, **opts)
                        s.say("Chromium opened in silent fallback mode")
                try:
                    s.loop(ctx)
                finally:
                    ctx.close()
        except Exception as e:
            s.error = str(e)
        finally:
            if own:
                WebEngine.profile_busy = False

    def serve(s, route):
        try:
            path = urllib.parse.unquote(urllib.parse.urlparse(route.request.url).path)
            if path == "/__home":
                return route.fulfill(status=200, content_type="text/html; charset=utf-8", body=home_html(s.vfs))
            data = s.vfs.read_bytes(path)
            ct = mimetypes.guess_type(path)[0] or "application/octet-stream"
            if ct == "text/html":
                data = data.decode("utf-8", "replace").replace("vm://home", HOME_URL).replace("vm:///", "http://vm.local/").encode("utf-8")
            route.fulfill(status=200, content_type=ct, body=data)
        except Exception:
            route.fulfill(status=404, content_type="text/plain", body="Not found on the virtual disk")

    def set_frame(s, b):
        s.frame, s.last_frame = b, time.time()
        s.fid += 1

    def on_cast(s, ev):
        s.set_frame(base64.b64decode(ev["data"]))
        s.ack = ev["sessionId"]

    def start_cast(s, cdp):
        cdp.send("Page.startScreencast", {"format": "jpeg", "quality": 75, "maxWidth": s.vp[0],
                                           "maxHeight": s.vp[1], "everyNthFrame": 1})

    def loop(s, ctx):
        page = ctx.pages[0] if ctx.pages else ctx.new_page()
        ctx.route("http://vm.local/**", s.serve)
        ctx.add_init_script(INIT_JS)

        def on_nav(f):
            if f == page.main_frame:
                s.url = f.url

        def on_req(r):
            try:
                if r.is_navigation_request() and r.frame == page.main_frame:
                    s.loading = True
            except Exception:
                pass

        def on_dialog(d):
            s.say(f"[{d.type}] {d.message[:100]}")
            d.accept()
        page.on("framenavigated", on_nav)
        page.on("request", on_req)
        page.on("load", lambda *_: setattr(s, "loading", False))
        page.on("domcontentloaded", lambda *_: setattr(s, "loading", False))
        page.on("dialog", on_dialog)
        def download(d):
            try:
                filename = os.path.basename(d.suggested_filename) or "download.bin"
                destination = HOME + "/Downloads/" + filename
                i = 1
                while s.vfs.get(destination):
                    stem, ext = os.path.splitext(filename)
                    destination = HOME + "/Downloads/" + stem + f" ({i})" + ext
                    i += 1
                with open(d.path(), "rb") as f:
                    s.vfs.write_bytes(destination, f.read())
                s.say("Saved " + os.path.basename(destination) + " to Downloads")
            except Exception as e:
                s.say("Download failed: " + str(e)[:90])
        page.on("download", download)
        cdp = ctx.new_cdp_session(page)
        cdp.on("Page.screencastFrame", s.on_cast)
        s.start_cast(cdp)
        last_title = 0.0
        while s.alive:
            cmds = []
            while True:
                try:
                    c = s.q.get_nowait()
                except queue.Empty:
                    break
                if cmds and c[0] == cmds[-1][0] == "move":
                    cmds[-1] = c
                elif cmds and c[0] == cmds[-1][0] == "wheel":
                    cmds[-1] = ("wheel", c[1], c[2], cmds[-1][3] + c[3], cmds[-1][4] + c[4])
                else:
                    cmds.append(c)
            for c in cmds:
                try:
                    s.exec(page, cdp, c)
                except Exception as e:
                    s.say(str(e).split("\n")[0][:120])
            page.wait_for_timeout(12)
            if s.ack is not None:
                sid, s.ack = s.ack, None
                try:
                    cdp.send("Page.screencastFrameAck", {"sessionId": sid})
                except Exception:
                    pass
            now = time.time()
            if now - s.last_frame > 1.0:  # fallback if screencast is silent
                try:
                    s.set_frame(page.screenshot(type="jpeg", quality=75))
                except Exception:
                    pass
            if now - last_title > 0.5:
                last_title = now
                try:
                    s.title = page.title()
                except Exception:
                    pass

    def exec(s, page, cdp, c):
        k = c[0]
        if k == "goto":
            s.url, s.loading = c[1], True
            try:
                page.goto(c[1], wait_until="commit", timeout=30000)
            except Exception as e:
                if "ERR_ABORTED" not in str(e):
                    page.set_content(ERR_TPL % html.escape(str(e).split("\n")[0]))
                    s.loading = False
        elif k == "back":
            page.go_back(wait_until="commit")
        elif k == "fwd":
            page.go_forward(wait_until="commit")
        elif k == "reload":
            s.loading = True
            page.reload(wait_until="commit")
        elif k == "stop":
            page.evaluate("window.stop()")
            s.loading = False
        elif k == "move":
            page.mouse.move(c[1], c[2])
        elif k in ("down", "up"):
            page.mouse.move(c[1], c[2])
            getattr(page.mouse, k)(button=c[3], click_count=c[4])
        elif k == "wheel":
            page.mouse.move(c[1], c[2])
            page.mouse.wheel(c[3], c[4])
        elif k == "type":
            page.keyboard.type(c[1])
        elif k == "press":
            page.keyboard.press(c[1])
        elif k == "paste":
            page.keyboard.insert_text(c[1])
        elif k == "copy":
            s.clip = page.evaluate("window.getSelection().toString()")
            s.clip_id += 1
        elif k == "resize":
            cdp.send("Page.stopScreencast")
            s.vp = (c[1], c[2])
            page.set_viewport_size({"width": c[1], "height": c[2]})
            s.start_cast(cdp)


class LiveBrowser(App):
    size = (960, 640)
    icon = ("W", (70, 150, 220))

    def __init__(s, vm, url="vm://home"):
        super().__init__(vm)
        s.engines, s.tab_index = [], 0
        s.new_tab(url)
        s.field, s.focus, s.fid, s.img, s.last_url, s.clip_id = TextField(url), "page", 0, None, "", 0
        s.vp, s.want, s.want_t, s.clk = s.eng.vp, None, 0.0, (0, (0, 0), 0)
        # First tab was started by new_tab().

    @property
    def eng(s):
        return s.engines[s.tab_index]

    def new_tab(s, url="vm://home"):
        engine = WebEngine(s.vm.vfs, max(100, s.size[0]), max(100, s.size[1] - 88), s.vm.config)
        s.engines.append(engine); s.tab_index = len(s.engines) - 1
        engine.start(); engine.cmd("goto", norm_live(url))
        s.field = TextField(url)
        s.last_url, s.fid, s.img, s.clip_id = "", 0, None, 0
        s.focus = "page"

    def switch_tab(s, index):
        if 0 <= index < len(s.engines):
            s.tab_index = index; s.last_url, s.fid, s.img = "", 0, None
            s.field = TextField(to_display(s.eng.url))
            s.focus = "page"

    def close_tab(s):
        if len(s.engines) == 1:
            s.vm.close(s.win); return
        s.engines.pop(s.tab_index).stop()
        s.switch_tab(min(s.tab_index, len(s.engines) - 1))

    @property
    def title(s):
        return "Browser - " + ((s.eng.title or to_display(s.eng.url)) or "Starting...")[:50]

    def on_close(s):
        for engine in s.engines: engine.stop()

    def navigate(s, t):
        s.eng.cmd("goto", norm_live(t))
        s.focus = "page"

    def bookmark(s):
        url = to_display(s.eng.url)
        if not url or url == "vm://home":
            return s.eng.say("Nothing to bookmark on this page")
        bm = get_bookmarks(s.vm.vfs)
        if url not in [u for _, u in bm]:
            bm.append((s.eng.title or url, url))
            try:
                s.vm.vfs.write(BOOKMARKS, json.dumps(bm))
            except VFSError:
                pass
        s.eng.say("Bookmarked: " + (s.eng.title or url)[:60])

    def update(s, dt):
        e = s.eng
        if e.fid != s.fid and e.frame:
            s.fid = e.fid
            try:
                s.img = pg.image.load(io.BytesIO(e.frame), "frame.jpg").convert()
            except Exception:
                pass
        if e.url != s.last_url:
            s.last_url = e.url
            if s.focus != "addr":
                s.field = TextField(to_display(e.url))
        if e.clip_id != s.clip_id:
            s.clip_id = e.clip_id
            put_clip(e.clip)
            e.say("Copied")
        if s.want and s.want != s.vp and time.time() - s.want_t > 0.3:
            s.vp = s.want
            e.cmd("resize", *s.want)

    def event(s, e, pos):
        if super().event(e, pos):
            return
        eng, t = s.eng, e.type
        if t == pg.MOUSEBUTTONDOWN:
            if pos[1] < 28:
                if pos[0] >= min(len(s.engines) * 135, max(0, s.win.rect.w - 42)):
                    s.new_tab()
                else:
                    s.switch_tab(min(len(s.engines) - 1, pos[0] // 135))
                return
            if pos[1] < 68:
                s.focus = "addr"
                s.field.c = len(s.field.t)
            elif e.button in (1, 2, 3):
                s.focus = "page"
                x, y, now = pos[0], pos[1] - 68, pg.time.get_ticks()
                lt, lp, cc = s.clk
                cc = cc + 1 if now - lt < 450 and abs(lp[0] - x) < 6 and abs(lp[1] - y) < 6 else 1
                s.clk = (now, (x, y), cc)
                eng.cmd("down", x, y, {1: "left", 2: "middle", 3: "right"}[e.button], cc)
        elif t == pg.MOUSEBUTTONUP and e.button in (1, 2, 3):
            eng.cmd("up", pos[0], pos[1] - 68, {1: "left", 2: "middle", 3: "right"}[e.button], s.clk[2])
        elif t == pg.MOUSEMOTION and pos[1] >= 68:
            eng.cmd("move", pos[0], pos[1] - 68)
        elif t == pg.MOUSEWHEEL and pos[1] >= 68:
            eng.cmd("wheel", pos[0], pos[1] - 68, getattr(e, "precise_x", e.x) * -100, getattr(e, "precise_y", e.y) * -100)
        elif t == pg.TEXTINPUT:
            if s.focus == "addr":
                s.field.key(e)
            else:
                eng.cmd("type", e.text)
        elif t == pg.KEYDOWN:
            mods, k = pg.key.get_mods(), e.key
            ctrl, shift = mods & pg.KMOD_CTRL, mods & pg.KMOD_SHIFT
            if ctrl and k == pg.K_l:
                s.focus, s.field.c = "addr", len(s.field.t)
            elif k == pg.K_F5 or (ctrl and k == pg.K_r):
                eng.cmd("reload")
            elif ctrl and k == pg.K_d:
                s.bookmark()
            elif s.focus == "addr":
                if ctrl and k == pg.K_v:
                    s.field.key(pg.event.Event(pg.TEXTINPUT, text=get_clip().replace("\n", " ")))
                    return
                r = s.field.key(e)
                if r == "enter":
                    s.navigate(s.field.t)
                elif r == "esc":
                    s.focus, s.field = "page", TextField(to_display(eng.url))
            elif ctrl and k == pg.K_c:
                eng.cmd("copy")
            elif ctrl and k == pg.K_v:
                if get_clip():
                    eng.cmd("paste", get_clip())
            elif ctrl and 32 <= k < 127:
                eng.cmd("press", "Control+" + chr(k))
            elif k in KEYMAP:
                eng.cmd("press", ("Shift+" if shift else "") + KEYMAP[k])

    def draw(s, surf):
        w, h = surf.get_size()
        eng = s.eng
        surf.fill((30, 32, 40))
        s.btns = []
        if eng.error and not eng.is_alive():
            return s.draw_error(surf, w, h)
        s.want, s.want_t = (w, max(50, h - 88)), (s.want_t if s.want == (w, max(50, h - 88)) else time.time())
        area = pg.Rect(0, 68, w, h - 88)
        if s.img:
            old = surf.get_clip()
            surf.set_clip(area)
            surf.blit(s.img, (0, 68))
            surf.set_clip(old)
        else:
            text(surf, "Starting browser engine...", "big", C["dim"], w // 2, h // 2, True)
        pg.draw.rect(surf, C["win"], (0, 0, w, 40))
        for i, (lbl, cb) in enumerate((("<", lambda: eng.cmd("back")), (">", lambda: eng.cmd("fwd")),
                                       ("X" if eng.loading else "R", lambda: eng.cmd("stop" if eng.loading else "reload")),
                                       ("H", lambda: s.navigate("vm://home")), ("+", s.bookmark))):
            s.button(surf, (6 + i * 32, 6, 28, 28), lbl, cb)
        s.field.draw(surf, (172, 34, w - 180, 28), caret=s.focus == "addr")
        if eng.loading:
            x = int(time.time() * 400) % (w + 120) - 120
            pg.draw.rect(surf, C["acc"], (max(0, x), 66, min(w, x + 120) - max(0, x), 2))
        pg.draw.rect(surf, C["win"], (0, h - 20, w, 20))
        st = eng.status if time.time() - eng.status_t < 4 else ("Loading " + to_display(eng.url) if eng.loading else "")
        text(surf, st[:140], "small", C["dim"], 8, h - 17)

    def draw_error(self, surf, w, h):
        lines = ["The web engine could not start.", "",
                 "Install the browser engine with these two commands, then reopen Browser:", "",
                 "    pip install -U playwright", "    playwright install chromium", "",
                 "Details: " + str(self.eng.error).split("\n")[0][:90]]
        for i, ln in enumerate(lines):
            text(surf, ln, "mono" if ln.startswith("    ") else "ui", C["yellow"] if i == 0 else C["txt"], 24, 30 + i * 24)
        self.button(surf, (24, 30 + len(lines) * 24 + 10, 240, 34), "Open basic text browser",
                    lambda: (self.vm.open("basic_browser"), self.vm.close(self.win)), bg=C["acc"])


# --------------------------------------------------------------------------- audio player
class Music(App):
    title = "Music"
    icon = ("♪", (175, 85, 145))
    size = (500, 300)

    def __init__(s, vm, path=None):
        super().__init__(vm)
        s.path, s.status, s.temp = path, "Click Browse to select an audio file", None
        if path: s.play()

    def browse(s):
        s.vm.open("files", path=HOME + "/Downloads", picker=s.select_file)

    def select_file(s, path):
        if path.lower().endswith((".mp3", ".wav", ".ogg")):
            s.path = path
            s.play()
        else:
            s.status = "Choose an MP3, WAV or OGG file"

    def play(s):
        if not s.path:
            s.status = "Select an MP3, WAV, or OGG file in Files"; return
        try:
            data = s.vm.vfs.read_bytes(s.path)
            ext = os.path.splitext(s.path)[1].lower()
            if ext not in (".mp3", ".wav", ".ogg"):
                raise ValueError("Supported: MP3, WAV, OGG")
            if not pg.mixer.get_init(): pg.mixer.init()
            if s.temp and os.path.exists(s.temp): os.unlink(s.temp)
            f = tempfile.NamedTemporaryFile(delete=False, suffix=ext)
            f.write(data); f.close(); s.temp = f.name
            pg.mixer.music.load(s.temp)
            pg.mixer.music.set_volume(0 if s.vm.config["mute"] else s.vm.config["volume"] / 100)
            pg.mixer.music.play()
            s.status = "Playing " + posixpath.basename(s.path)
        except Exception as e: s.status = "Playback failed: " + str(e)

    def stop(s):
        try: pg.mixer.music.stop()
        except Exception: pass
        s.status = "Stopped"

    def on_close(s):
        s.stop()
        if s.temp:
            try: os.unlink(s.temp)
            except OSError: pass

    def draw(s, surf):
        w, h = surf.get_size(); surf.fill(C["win"]); s.btns = []
        text(surf, "Audio Player", "h2", C["txt"], 20, 20)
        text(surf, (s.path or "No file selected")[-70:], "ui", C["dim"], 20, 80)
        s.button(surf, (20, 120, 125, 38), "Browse Files", s.browse, bg=C["acc"])
        s.button(surf, (20, 165, 125, 32), "Play / Restart", s.play)
        s.button(surf, (155, 120, 100, 38), "Pause", lambda: pg.mixer.music.pause())
        s.button(surf, (265, 120, 100, 38), "Resume", lambda: pg.mixer.music.unpause())
        s.button(surf, (375, 120, 95, 38), "Stop", s.stop)
        text(surf, s.status[:76], "ui", C["txt"], 20, 200)
        text(surf, "Browse opens Files; selecting audio closes the picker.", "small", C["dim"], 20, 245)


# --------------------------------------------------------------------------- system utilities
class Settings(App):
    title = "Settings"
    icon = ("S", (100, 115, 220))
    size = (590, 550)

    def __init__(s, vm):
        super().__init__(vm)

    def draw(s, surf):
        w, h = surf.get_size(); surf.fill(C["win"]); s.btns = []
        text(surf, "Personalization & system", "h2", C["txt"], 20, 18)
        text(surf, "Wallpaper", "b", C["dim"], 20, 70)
        for i, (name, _) in enumerate(s.vm.wallpapers):
            s.button(surf, (20 + i * 124, 96, 116, 32), name,
                     lambda i=i: s.vm.set_wallpaper(i),
                     bg=C["acc"] if s.vm.config["wallpaper"] == i else C["btn"])
        text(surf, "Audio volume", "b", C["dim"], 20, 157)
        s.button(surf, (20, 182, 55, 30), "-", lambda: s.vm.set_volume(s.vm.config["volume"] - 10))
        text(surf, str(s.vm.config["volume"]) + "%", "b", C["txt"], 90, 188)
        s.button(surf, (160, 182, 55, 30), "+", lambda: s.vm.set_volume(s.vm.config["volume"] + 10))
        s.button(surf, (234, 182, 90, 30), "Mute" if not s.vm.config["mute"] else "Unmute", s.vm.toggle_mute)
        text(surf, "Display", "b", C["dim"], 20, 241)
        s.button(surf, (20, 265, 155, 32), "Fullscreen (F11)", s.vm.toggle_fullscreen)
        s.button(surf, (184, 265, 155, 32), "Fit to desktop", s.vm.fit_display)
        now = datetime.datetime.now() + datetime.timedelta(minutes=s.vm.config["time_offset"])
        text(surf, "Virtual date & time: " + now.strftime("%Y-%m-%d %H:%M"), "ui", C["txt"], 20, 322)
        s.button(surf, (20, 350, 135, 30), "Time -1 hour", lambda: s.vm.change_time(-60))
        s.button(surf, (163, 350, 135, 30), "Time +1 hour", lambda: s.vm.change_time(60))
        text(surf, "Chromium sound", "b", C["dim"], 20, 392)
        s.button(surf, (160, 388, 165, 30), "Audio ON" if s.vm.config.get("browser_audio", True) else "Audio OFF",
                 lambda: (s.vm.config.__setitem__("browser_audio", not s.vm.config.get("browser_audio", True)), s.vm.save_config()))
        text(surf, "Restart browser tabs to apply audio setting", "small", C["dim"], 335, 396)
        s.button(surf, (20, 422, 145, 29), "Custom wallpaper...", s.vm.choose_wallpaper)
        text(surf, "Changes affect PyVM only, not your computer's clock.", "small", C["dim"], 20, h - 26)


class TaskManager(App):
    title = "Task Manager"
    icon = ("T", (60, 165, 145))
    size = (660, 480)

    def __init__(s, vm):
        super().__init__(vm); s.selected = None; s.rows = []; s.message = ""

    def event(s, e, pos):
        if super().event(e, pos): return
        if e.type == pg.MOUSEBUTTONDOWN and e.button == 1 and pos[1] >= 106:
            i = (pos[1] - 106) // 30
            if 0 <= i < len(s.rows): s.selected = s.rows[i]

    def end_selected(s):
        if s.selected in s.vm.windows:
            if s.selected is s.win:
                s.vm.close(s.win); return
            s.vm.close(s.selected); s.message = "Task ended"
            s.selected = None
        else: s.message = "Select a running app"

    def draw(s, surf):
        w, h = surf.get_size(); surf.fill(C["win"]); s.btns = []
        s.rows = list(s.vm.windows)
        text(surf, "Running applications", "h2", C["txt"], 16, 16)
        s.button(surf, (w - 135, 14, 119, 32), "End task", s.end_selected, bg=C["red"])
        text(surf, f"{len(s.rows)} apps  |  uptime {int(time.time()-BOOT_TIME)}s", "ui", C["dim"], 16, 58)
        text(surf, "APPLICATION", "small", C["dim"], 24, 86)
        text(surf, "STATUS", "small", C["dim"], w - 125, 86)
        for i, win in enumerate(s.rows[:max(1,(h - 145)//30)]):
            y = 106 + i * 30
            pg.draw.rect(surf, C["barf"] if win is s.selected else C["bar"], (16, y, w - 32, 28), border_radius=4)
            text(surf, win.app.title[:55], "ui", C["txt"], 24, y + 5)
            text(surf, "Minimized" if win.min else "Running", "small", C["dim"], w - 125, y + 6)
        text(surf, s.message or "Select an app, then End task to close it.", "small", C["dim"], 16, h - 24)


# --------------------------------------------------------------------------- window manager / desktop
APPS = dict(terminal=Terminal, files=Files, notepad=Notepad, calculator=Calculator, clock=Clock, browser=LiveBrowser, music=Music, settings=Settings, task_manager=TaskManager)
EXTRA = dict(basic_browser=BasicBrowser)
ALIASES = dict(calc="calculator", explorer="files", edit="notepad", web="browser", term="terminal", tasks="task_manager", taskmgr="task_manager")
APP_LABELS = dict(terminal="Terminal", files="Files", notepad="Notepad", calculator="Calculator", clock="Clock",
                  browser="Browser", music="Music", settings="Settings", task_manager="Task Manager")


class Window:
    TH = 26

    def __init__(s, app, x, y):
        s.app, s.min, s.max, s.prev, s.surf = app, False, False, None, None
        s.rect = pg.Rect(x, y, app.size[0], app.size[1] + s.TH)
        app.win = s

    def content(s):
        return pg.Rect(s.rect.x, s.rect.y + s.TH, s.rect.w, s.rect.h - s.TH)

    def btn(s, i):  # 0 close, 1 maximize, 2 minimize
        return pg.Rect(s.rect.right - 28 - i * 26, s.rect.y + 3, 22, 20)


class VM:
    def __init__(s):
        pg.init()
        pg.display.set_caption("PyVM")
        global W, H
        info = pg.display.Info()
        W, H = max(800, info.current_w), max(550, info.current_h)
        s.fullscreen = False
        s.scr = pg.display.set_mode((W, H), pg.RESIZABLE)
        try:
            pg.key.start_text_input()
        except Exception:
            pass
        pg.key.set_repeat(400, 35)
        load_fonts()
        s.vfs = VFS(DISK)
        s.config_path = os.path.join(os.path.dirname(DISK), "vm_settings.json")
        s.config = {"wallpaper": 0, "volume": 70, "mute": False, "time_offset": 0, "browser_audio": True, "desktop_positions": {}, "custom_wallpaper": ""}
        try:
            with open(s.config_path, encoding="utf-8") as f: s.config.update(json.load(f))
        except (OSError, ValueError): pass
        # Drop old icon overrides, including broken image icon paths.
        s.config.pop("app_icons", None)
        s.config.pop("app_icon_images", None)
        s.wallpapers = [("Blue", (28, 43, 96)), ("Green", (21, 78, 65)),
                        ("Purple", (75, 36, 100)), ("Charcoal", (35, 39, 47))]
        s.set_volume(s.config["volume"])
        s.windows, s.drag, s.resize, s.start_open = [], None, None, False
        s.tray_menu, s.volume_drag = None, False
        s.sel_icon, s.last_click, s.cascade, s.boot = None, (0, None), 0, 0.0
        s.desktop_drag, s.desktop_moved = None, False
        s.wall = s.make_wallpaper()

    def save_config(s):
        try:
            with open(s.config_path, "w", encoding="utf-8") as f: json.dump(s.config, f)
        except OSError: pass

    def app_icon(s, key):
        return APPS[key].icon

    def draw_app_icon(s, surface, key, rect, glyph, color):
        pg.draw.rect(surface, color, rect, border_radius=max(3, min(8, rect.w // 4)))
        # Use a font that actually fits small launcher icons.
        font = F["small"] if rect.w < 32 else F["big"]
        label = str(glyph)[:3]
        img = font.render(label, True, (255, 255, 255))
        if img.get_width() > rect.w - 3 or img.get_height() > rect.h - 3:
            k = min((rect.w - 4) / max(1, img.get_width()), (rect.h - 4) / max(1, img.get_height()))
            img = pg.transform.smoothscale(img, (max(1, int(img.get_width()*k)), max(1, int(img.get_height()*k))))
        surface.blit(img, img.get_rect(center=rect.center))

    def choose_wallpaper(s):
        try:
            from tkinter import Tk, filedialog
            root = Tk(); root.withdraw(); root.attributes("-topmost", True)
            chosen = filedialog.askopenfilename(parent=root, filetypes=[("Images", "*.png *.jpg *.jpeg *.bmp *.webp"), ("All files", "*.*")])
            root.destroy()
            if chosen:
                pg.image.load(chosen)
                s.config["custom_wallpaper"] = chosen
                s.wall = s.make_wallpaper()
                s.save_config()
        except Exception as e:
            print("Wallpaper selection failed:", e)

    def set_wallpaper(s, i):
        s.config["wallpaper"] = i % len(s.wallpapers)
        s.config["custom_wallpaper"] = ""
        s.wall = s.make_wallpaper(); s.save_config()

    def set_volume(s, v):
        s.config["volume"] = max(0, min(100, int(v)))
        try: pg.mixer.music.set_volume(0 if s.config["mute"] else s.config["volume"] / 100)
        except Exception: pass
        s.save_config()

    def toggle_mute(s):
        s.config["mute"] = not s.config["mute"]; s.set_volume(s.config["volume"])

    def change_time(s, mins):
        s.config["time_offset"] += mins; s.save_config()

    def fit_display(s):
        global W, H
        info = pg.display.Info()
        W, H = max(800, info.current_w), max(550, info.current_h)
        s.fullscreen = False
        s.scr = pg.display.set_mode((W, H), pg.RESIZABLE)
        s.wall = s.make_wallpaper()
        for win in s.windows:
            if win.max: win.rect = pg.Rect(0, 0, W, H - TASK)

    def toggle_fullscreen(s):
        global W, H
        s.fullscreen = not s.fullscreen
        if s.fullscreen:
            info = pg.display.Info(); W, H = info.current_w, info.current_h
            s.scr = pg.display.set_mode((W, H), pg.FULLSCREEN)
        else:
            s.scr = pg.display.set_mode((W, H), pg.RESIZABLE)
        s.wall = s.make_wallpaper()
        for win in s.windows:
            if win.max: win.rect = pg.Rect(0, 0, W, H - TASK)

    def make_wallpaper(s):
        custom = s.config.get("custom_wallpaper")
        if custom:
            try:
                image = pg.image.load(custom)
                return pg.transform.smoothscale(image, (W, H))
            except (OSError, pg.error):
                pass
        surf = pg.Surface((W, H))
        color = s.wallpapers[s.config["wallpaper"] % len(s.wallpapers)][1]
        for y in range(H):
            t = y / max(1, H)
            pg.draw.line(surf, tuple(min(255, int(v * (0.7 + 0.55 * t))) for v in color), (0, y), (W, y))
        for cx, cy, r, col in ((int(W*.8), int(H*.3), 260, (90, 110, 180)), (int(W*.85), int(H*.75), 200, (80, 95, 160)), (int(W*.45), int(H*.18), 150, (70, 120, 160))):
            circ = pg.Surface((r * 2, r * 2), pg.SRCALPHA)
            pg.draw.circle(circ, col + (50,), (r, r), r)
            surf.blit(circ, (cx - r, cy - r))
        return surf

    # ---- app launching
    def open(s, name, **kw):
        name = ALIASES.get(name, name)
        app = (APPS.get(name) or EXTRA[name])(s, **kw)
        win = Window(app, 60 + s.cascade * 28, 40 + s.cascade * 28)
        win.rect.w = min(win.rect.w, W - 40)
        win.rect.h = min(win.rect.h, H - TASK - 40)
        s.cascade = (s.cascade + 1) % 8
        s.windows.append(win)
        return app

    def open_target(s, t, cwd="/"):
        name = ALIASES.get(t, t)
        if name in APPS:
            return s.open(name)
        p = s.vfs.norm(t, cwd)
        if s.vfs.isdir(p):
            s.open("files", path=p)
        elif s.vfs.isfile(p):
            if p.lower().endswith((".mp3", ".wav", ".ogg")):
                s.open("music", path=p)
            elif p.endswith((".html", ".htm")):
                s.open("browser", url="vm://" + p)
            else:
                s.open("notepad", path=p)
        else:
            raise VFSError(f"{t}: no such app, file or directory")

    def close(s, w):
        if w in s.windows:
            s.windows.remove(w)
            getattr(w.app, "on_close", lambda: None)()

    def focus(s, w):
        s.windows.remove(w)
        s.windows.append(w)
        w.min = False

    def top(s):
        return next((w for w in reversed(s.windows) if not w.min), None)

    # ---- desktop icons
    def desk_items(s):
        its = [(APP_LABELS[n], s.app_icon(n), ("app", n)) for n in APPS]
        try:
            for n, v in s.vfs.listdir(HOME + "/Desktop"):
                its.append((n, None if v["t"] == "d" else False, ("file", f"{HOME}/Desktop/{n}")))
        except VFSError:
            pass
        positions = s.config.setdefault("desktop_positions", {})
        count = max(1, (H - TASK - 24) // 92)
        result = []
        for i, (label, icon, target) in enumerate(its):
            key = target[0] + ":" + target[1]
            saved = positions.get(key)
            default = (14 + (i // count) * 96, 14 + (i % count) * 92)
            x, y = saved if isinstance(saved, list) and len(saved) == 2 and all(isinstance(v, (int, float)) for v in saved) else default
            rect = pg.Rect(max(0, min(W - 88, int(x))), max(0, min(H - TASK - 86, int(y))), 88, 86)
            result.append((label, icon, target, rect))
        return result

    def launch(s, tg):
        try:
            s.open(tg[1]) if tg[0] == "app" else s.open_target(tg[1])
        except VFSError:
            pass

    def shutdown(s):
        for w in list(s.windows):
            s.close(w)
        s.vfs.save()
        s.save_config()
        pg.quit()
        sys.exit()

    def restart(s):
        for w in list(s.windows):
            s.close(w)
        s.boot, s.start_open = 0.0, False

    # ---- events
    def menu_rect(s):
        n = len(APPS) + 2
        return pg.Rect(6, H - TASK - n * 34 - 10, 220, n * 34 + 10)

    def tray_hitboxes(s):
        y = H - TASK + 3
        return {"battery": pg.Rect(W - 276, y, 94, TASK - 5),
                "volume": pg.Rect(W - 178, y, 79, TASK - 5)}

    def tray_rect(s):
        return pg.Rect(max(5, W - 310), H - TASK - 151, 294, 144)

    def volume_from_x(s, x):
        r = s.tray_rect()
        s.set_volume(round(max(0, min(1, (x - r.x - 20) / (r.w - 40))) * 100))

    def battery_status(s):
        # psutil is preferred; Windows API works even when psutil is absent.
        try:
            import psutil
            battery = psutil.sensors_battery()
            if battery is not None and battery.percent is not None:
                return f"{round(battery.percent)}%", ("Charging / plugged in" if battery.power_plugged else "On battery")
        except (ImportError, OSError, AttributeError):
            pass
        if sys.platform == "win32":
            try:
                import ctypes
                class PowerStatus(ctypes.Structure):
                    _fields_ = [("ACLineStatus", ctypes.c_ubyte), ("BatteryFlag", ctypes.c_ubyte),
                                ("BatteryLifePercent", ctypes.c_ubyte), ("SystemStatusFlag", ctypes.c_ubyte),
                                ("BatteryLifeTime", ctypes.c_ulong), ("BatteryFullLifeTime", ctypes.c_ulong)]
                status = PowerStatus()
                if ctypes.windll.kernel32.GetSystemPowerStatus(ctypes.byref(status)) and status.BatteryLifePercent != 255:
                    return f"{status.BatteryLifePercent}%", ("Plugged in" if status.ACLineStatus == 1 else "On battery")
            except Exception:
                pass
        if sys.platform.startswith("linux"):
            try:
                from pathlib import Path
                for path in Path("/sys/class/power_supply").glob("BAT*"):
                    capacity = int((path / "capacity").read_text().strip())
                    status = (path / "status").read_text().strip()
                    return f"{capacity}%", status
            except (OSError, ValueError):
                pass
        return "N/A", "No battery reported by the host OS (desktop PC or unsupported device)"

    def draw_tray(s):
        if not s.tray_menu: return
        r = s.tray_rect()
        pg.draw.rect(s.scr, (30, 33, 45), r, border_radius=9)
        pg.draw.rect(s.scr, C["line"], r, 1, border_radius=9)
        if s.tray_menu == "volume":
            text(s.scr, "Volume", "b", C["txt"], r.x + 16, r.y + 13)
            text(s.scr, f"{s.config['volume']}%", "ui", C["txt"], r.right - 53, r.y + 14)
            bar = pg.Rect(r.x + 20, r.y + 64, r.w - 40, 10)
            pg.draw.rect(s.scr, C["field"], bar, border_radius=5)
            pg.draw.rect(s.scr, C["acc"], (bar.x, bar.y, int(bar.w * s.config["volume"] / 100), bar.h), border_radius=5)
            pg.draw.circle(s.scr, C["txt"], (bar.x + int(bar.w * s.config["volume"] / 100), bar.centery), 9)
            btn = pg.Rect(r.x + 15, r.y + 95, 100, 29)
            pg.draw.rect(s.scr, C["btn"], btn, border_radius=5)
            text(s.scr, "Unmute" if s.config["mute"] else "Mute", "ui", C["txt"], btn.x + 13, btn.y + 5)
        else:
            percent, detail = s.battery_status()
            text(s.scr, "Battery: " + percent, "b", C["txt"], r.x + 14, r.y + 16)
            text(s.scr, detail[:42], "ui", C["dim"], r.x + 14, r.y + 50)
            text(s.scr, "Uses your host computer's battery", "small", C["dim"], r.x + 14, r.y + 80)

    def on_down(s, e):
        x, y = e.pos
        if e.button != 1:
            if y < H - TASK and not s.start_open:
                for w in reversed(s.windows):
                    if not w.min and w.rect.collidepoint(x, y):
                        c = w.content()
                        if c.collidepoint(x, y):
                            w.app.event(e, (x - c.x, y - c.y))
                        break
            return
        if s.tray_menu:
            menu = s.tray_rect()
            if menu.collidepoint(x, y):
                if s.tray_menu == "volume":
                    if pg.Rect(menu.x + 10, menu.y + 54, menu.w - 20, 32).collidepoint(x, y):
                        s.volume_drag = True; s.volume_from_x(x)
                    elif pg.Rect(menu.x + 15, menu.y + 95, 100, 29).collidepoint(x, y):
                        s.toggle_mute()
                elif s.tray_menu == "battery":
                    pass
                return
            s.tray_menu = None
        if y >= H - TASK:
            if pg.Rect(6, H - TASK + 4, 78, 28).collidepoint(x, y):
                s.start_open = not s.start_open; return
            for name, rect in s.tray_hitboxes().items():
                if rect.collidepoint(x, y):
                    s.start_open = False; s.tray_menu = name; return
            bx = 96
            bw = max(66, min(150, (W - 385 - bx) // max(1, len(s.windows)) - 6))
            for w in s.windows:
                if pg.Rect(bx, H - TASK + 4, bw, 28).collidepoint(x, y):
                    if s.top() is w:
                        w.min = True
                    else:
                        s.focus(w)
                bx += bw + 6
            return
        if s.start_open:
            mr = s.menu_rect()
            if mr.collidepoint(x, y):
                i = (y - mr.y - 5) // 34
                names = list(APPS)
                if 0 <= i < len(names):
                    s.open(names[i])
                elif i == len(names):
                    s.restart()
                elif i == len(names) + 1:
                    s.shutdown()
            s.start_open = False
            return
        for w in reversed(s.windows):
            if w.min or not w.rect.collidepoint(x, y):
                continue
            s.focus(w)
            if w.btn(0).collidepoint(x, y):
                s.close(w)
            elif w.btn(1).collidepoint(x, y):
                s.toggle_max(w)
            elif w.btn(2).collidepoint(x, y):
                w.min = True
            elif y < w.rect.y + w.TH:
                if not w.max:
                    s.drag = (w, x - w.rect.x, y - w.rect.y)
            elif x > w.rect.right - 14 and y > w.rect.bottom - 14 and not w.max:
                s.resize = (w, x - w.rect.w, y - w.rect.h)
            else:
                c = w.content()
                w.app.event(e, (x - c.x, y - c.y))
            return
        # desktop
        hit = next((it for it in s.desk_items() if it[3].collidepoint(x, y)), None)
        now = pg.time.get_ticks()
        if hit:
            if s.last_click[1] == hit[2] and now - s.last_click[0] < 450:
                s.launch(hit[2])
                s.desktop_drag = None
            else:
                s.desktop_drag = (hit[2], x - hit[3].x, y - hit[3].y, x, y)
                s.desktop_moved = False
            s.sel_icon, s.last_click = hit[2], (now, hit[2])
        else:
            s.sel_icon = None

    def toggle_max(s, w):
        if w.max:
            w.rect, w.max = w.prev, False
        else:
            w.prev, w.rect, w.max = w.rect.copy(), pg.Rect(0, 0, W, H - TASK), True

    def handle(s, e):
        if e.type == pg.QUIT:
            s.shutdown()
        if e.type == pg.VIDEORESIZE and not s.fullscreen:
            global W, H
            W, H = max(800, e.w), max(550, e.h)
            s.scr = pg.display.set_mode((W, H), pg.RESIZABLE)
            s.wall = s.make_wallpaper()
            for win in s.windows:
                if win.max: win.rect = pg.Rect(0, 0, W, H - TASK)
        if e.type == pg.KEYDOWN and e.key == pg.K_F11:
            s.toggle_fullscreen(); return
        if e.type == pg.KEYDOWN and e.key == pg.K_ESCAPE and s.fullscreen:
            s.toggle_fullscreen(); return
        if s.boot < 3.0:
            if e.type in (pg.KEYDOWN, pg.MOUSEBUTTONDOWN):
                s.boot = 3.0
            return
        if e.type == pg.MOUSEBUTTONDOWN:
            s.on_down(e)
        elif e.type == pg.MOUSEBUTTONUP:
            if s.desktop_drag:
                if s.desktop_moved:
                    s.save_config()
                s.desktop_drag = None
            s.volume_drag = False
            s.drag = s.resize = None
            t = s.top()
            if t:
                c = t.content()
                t.app.event(e, (e.pos[0] - c.x, e.pos[1] - c.y))
        elif e.type == pg.MOUSEMOTION:
            x, y = e.pos
            if s.volume_drag:
                s.volume_from_x(x); return
            if s.desktop_drag and e.buttons[0]:
                target, dx, dy, sx, sy = s.desktop_drag
                if abs(x - sx) + abs(y - sy) > 5:
                    s.desktop_moved = True
                if s.desktop_moved:
                    key = target[0] + ":" + target[1]
                    s.config.setdefault("desktop_positions", {})[key] = [max(0, min(W - 88, x - dx)), max(0, min(H - TASK - 86, y - dy))]
                return
            if s.drag:
                w, dx, dy = s.drag
                w.rect.x, w.rect.y = x - dx, max(0, min(H - TASK - 26, y - dy))
            elif s.resize:
                w, dx, dy = s.resize
                w.rect.w, w.rect.h = max(260, x - dx), max(180, y - dy)
            else:
                tw = s.top()
                hit = [tw] if tw and e.buttons[0] else [w for w in reversed(s.windows) if not w.min and w.rect.collidepoint(x, y)][:1]
                for w in hit:
                    c = w.content()
                    w.app.event(e, (x - c.x, y - c.y))
        elif e.type == pg.MOUSEWHEEL:
            x, y = pg.mouse.get_pos()
            for w in reversed(s.windows):
                if not w.min and w.rect.collidepoint(x, y):
                    c = w.content()
                    w.app.event(e, (x - c.x, y - c.y))
                    break
        elif e.type in (pg.KEYDOWN, pg.TEXTINPUT):
            t = s.top()
            if t:
                t.app.event(e, None)

    # ---- drawing
    def draw_boot(s):
        s.scr.fill((0, 0, 0))
        lines = ["PyVM BIOS v1.0", "Checking memory............ OK", f"Mounting virtual disk ({os.path.basename(DISK)}).. OK",
                 "Starting window manager..... OK", "Starting services........... OK", "", "Welcome to PyVM. (press any key to skip)"]
        for i, ln in enumerate(lines[:int(s.boot / 0.4) + 1]):
            text(s.scr, ln, "mono", (200, 255, 200), 24, 24 + i * 22)

    def draw_window(s, w, focus):
        r = w.rect
        pg.draw.rect(s.scr, (12, 13, 18), r.inflate(4, 4), border_radius=9)
        pg.draw.rect(s.scr, C["barf"] if focus else C["bar"], (r.x, r.y, r.w, w.TH), border_top_left_radius=8, border_top_right_radius=8)
        text(s.scr, w.app.title[:60], "ui", C["txt"], r.x + 10, r.y + 5)
        for i, (col, g) in enumerate(((C["red"], "x"), (C["btn"], "□"), (C["btn"], "_"))):
            b = w.btn(i)
            pg.draw.rect(s.scr, col if not b.collidepoint(pg.mouse.get_pos()) else lighten(col, 30), b, border_radius=5)
            if i == 0:
                pg.draw.line(s.scr, C["txt"], (b.x + 7, b.y + 6), (b.right - 7, b.bottom - 6), 2)
                pg.draw.line(s.scr, C["txt"], (b.x + 7, b.bottom - 6), (b.right - 7, b.y + 6), 2)
            elif i == 1:
                pg.draw.rect(s.scr, C["txt"], (b.x + 6, b.y + 5, 10, 10), 2)
            else:
                pg.draw.line(s.scr, C["txt"], (b.x + 6, b.bottom - 6), (b.right - 6, b.bottom - 6), 2)
        c = w.content()
        if w.surf is None or w.surf.get_size() != c.size:
            w.surf = pg.Surface(c.size)
        w.app.draw(w.surf)
        s.scr.blit(w.surf, c.topleft)
        if not w.max:
            pg.draw.polygon(s.scr, C["dim"], [(r.right - 3, r.bottom - 12), (r.right - 3, r.bottom - 3), (r.right - 12, r.bottom - 3)])

    def draw(s):
        if s.boot < 3.0:
            return s.draw_boot()
        s.scr.blit(s.wall, (0, 0))
        for label, ic, tg, r in s.desk_items():
            if s.sel_icon == tg:
                pg.draw.rect(s.scr, (255, 255, 255, 40), r, border_radius=8, width=2)
            box = pg.Rect(r.centerx - 24, r.y + 6, 48, 48)
            if tg[0] == "app":
                s.draw_app_icon(s.scr, tg[1], box, ic[0], ic[1])
            else:
                draw_file_icon(s.scr, "dir" if ic is None else "file", box.x + 6, box.y + 6, 36)
            lbl = label if len(label) < 13 else label[:11] + ".."
            text(s.scr, lbl, "ui", (0, 0, 0), r.centerx + 1, r.y + 61, True)
            text(s.scr, lbl, "ui", (255, 255, 255), r.centerx, r.y + 60, True)
        top = s.top()
        for w in s.windows:
            if not w.min:
                s.draw_window(w, w is top)
        # taskbar
        pg.draw.rect(s.scr, (22, 24, 32), (0, H - TASK, W, TASK))
        pg.draw.line(s.scr, C["line"], (0, H - TASK), (W, H - TASK))
        sb = pg.Rect(6, H - TASK + 4, 78, 28)
        pg.draw.rect(s.scr, C["acc"] if s.start_open else C["btn"], sb, border_radius=6)
        text(s.scr, "PyVM", "b", C["txt"], sb.centerx, sb.y + 4, True)
        bx = 96
        bw = max(66, min(150, (W - 385 - bx) // max(1, len(s.windows)) - 6))
        for w in s.windows:
            if bx + bw > W - 285: break
            r = pg.Rect(bx, H - TASK + 4, bw, 28)
            pg.draw.rect(s.scr, C["barf"] if w is top else C["btn"], r, border_radius=6)
            text(s.scr, w.app.title[:max(5, bw // 8 - 2)], "ui", C["txt"] if not w.min else C["dim"], r.x + 8, r.y + 6)
            bx += bw + 6
        now = datetime.datetime.now() + datetime.timedelta(minutes=s.config["time_offset"])
        battery, _ = s.battery_status()
        hits = s.tray_hitboxes()
        for key, label in (("battery", "BAT " + battery), ("volume", "Mute" if s.config["mute"] else f"Vol {s.config['volume']}%")):
            r = hits[key]
            if s.tray_menu == key or r.collidepoint(pg.mouse.get_pos()):
                pg.draw.rect(s.scr, C["btn"], r, border_radius=5)
            text(s.scr, label, "small", C["txt"], r.x + 5, r.y + 10)
        text(s.scr, now.strftime("%H:%M"), "b", C["txt"], W - 12 - F["b"].size("00:00")[0], H - TASK + 3)
        text(s.scr, now.strftime("%b %d"), "small", C["dim"], W - 12 - F["small"].size("Oct 00")[0], H - TASK + 20)
        s.draw_tray()
        if s.start_open:
            mr = s.menu_rect()
            pg.draw.rect(s.scr, (28, 30, 40), mr, border_radius=8)
            pg.draw.rect(s.scr, C["line"], mr, 1, border_radius=8)
            items = [(APP_LABELS[n], s.app_icon(n)) for n in APPS] + [("Restart", None), ("Shut down", None)]
            mx, my = pg.mouse.get_pos()
            for i, (lbl, ic) in enumerate(items):
                r = pg.Rect(mr.x + 5, mr.y + 5 + i * 34, mr.w - 10, 32)
                if r.collidepoint(mx, my):
                    pg.draw.rect(s.scr, C["barf"], r, border_radius=6)
                if ic:
                    key = list(APPS)[i] if i < len(APPS) else ""
                    if key: s.draw_app_icon(s.scr, key, pg.Rect(r.x + 6, r.y + 5, 22, 22), ic[0], ic[1])
                text(s.scr, lbl, "ui", C["red"] if lbl == "Shut down" else C["txt"], r.x + 38, r.y + 8)

    def run(s):
        clock = pg.time.Clock()
        while True:
            dt = clock.tick(60) / 1000
            for e in pg.event.get():
                s.handle(e)
            if s.boot < 3.0:
                s.boot += dt
                if s.boot >= 3.0 and not s.windows:
                    s.open("terminal")
            for w in list(s.windows):
                w.app.update(dt)
            s.draw()
            pg.display.flip()


if __name__ == "__main__":
    VM().run()