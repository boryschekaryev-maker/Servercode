"""Experimental single-user browser adapter for PyVM (pygame)."""
import io
import os
import queue
import threading
import time
from functools import wraps

# SDL dummy driver renders pygame to an offscreen surface on Linux servers.
os.environ.setdefault('SDL_VIDEODRIVER', 'dummy')
os.environ.setdefault('SDL_AUDIODRIVER', 'dummy')

from flask import Flask, Response, abort, jsonify, render_template_string, request
from PIL import Image
import pygame as pg
import pyvm

app = Flask(__name__)
TOKEN = os.environ.get('PYVM_TOKEN', '')
if not TOKEN:
    raise RuntimeError('Set PYVM_TOKEN to a long random secret before starting the server')

WIDTH, HEIGHT = 1100, 700
commands = queue.Queue(maxsize=500)
latest_frame = None
frame_lock = threading.Lock()
mouse_pos = (0, 0)
mouse_down = False

PAGE = '''<!doctype html><html><head><meta name="viewport" content="width=device-width,initial-scale=1">
<title>PyVM Web</title><style>body{margin:0;background:#10131b;color:white;font:14px system-ui;text-align:center}header{padding:10px}img{width:min(100%,1100px);height:auto;display:block;margin:auto;touch-action:none;outline:1px solid #39445b}button{padding:8px;margin:4px}small{color:#b5c0d3}</style></head><body>
<header>PyVM Web — experimental single-user session <small>(click the desktop to type)</small></header>
<img id="screen" src="/stream?token={{token}}" tabindex="0" alt="PyVM desktop">
<button id="focus">Focus keyboard</button><button id="reload">Reconnect image</button>
<script>
const token={{token|tojson}}, screen=document.querySelector('#screen');
const send=(obj)=>fetch('/input?token='+encodeURIComponent(token),{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(obj)}).catch(()=>{});
function coords(e){let r=screen.getBoundingClientRect();return {x:Math.max(0,Math.min(1099,Math.floor((e.clientX-r.left)*1100/r.width))),y:Math.max(0,Math.min(699,Math.floor((e.clientY-r.top)*700/r.height)))}}
screen.addEventListener('pointerdown',e=>{screen.focus();screen.setPointerCapture(e.pointerId);send({type:'mouse',action:'down',...coords(e)});e.preventDefault()});
screen.addEventListener('pointermove',e=>{send({type:'mouse',action:'move',...coords(e)})});
screen.addEventListener('pointerup',e=>{send({type:'mouse',action:'up',...coords(e)})});
screen.addEventListener('wheel',e=>{send({type:'wheel',y:e.deltaY>0?-1:1,...coords(e)});e.preventDefault()},{passive:false});
screen.addEventListener('keydown',e=>{send({type:'key',action:'down',key:e.key,ctrl:e.ctrlKey,shift:e.shiftKey,alt:e.altKey});if(e.key.length===1&&!e.ctrlKey&&!e.metaKey&&!e.altKey)send({type:'text',text:e.key});e.preventDefault()});
screen.addEventListener('keyup',e=>{send({type:'key',action:'up',key:e.key,ctrl:e.ctrlKey,shift:e.shiftKey,alt:e.altKey});e.preventDefault()});
document.querySelector('#focus').onclick=()=>screen.focus();document.querySelector('#reload').onclick=()=>{screen.src='/stream?token='+encodeURIComponent(token)+'&t='+Date.now()};
</script></body></html>'''

def protected(fn):
    @wraps(fn)
    def inner(*a, **kw):
        if request.args.get('token') != TOKEN:
            abort(403)
        return fn(*a, **kw)
    return inner

@app.get('/')
@protected
def index():
    return render_template_string(PAGE, token=TOKEN)

@app.post('/input')
@protected
def input_event():
    data = request.get_json(silent=True)
    if not isinstance(data, dict) or data.get('type') not in ('mouse','wheel','key','text'):
        abort(400)
    try:
        commands.put_nowait(data)
    except queue.Full:
        return jsonify(error='input queue full'), 429
    return jsonify(ok=True)

@app.get('/stream')
@protected
def stream():
    def frames():
        while True:
            with frame_lock:
                jpg = latest_frame
            if jpg:
                yield b'--frame\r\nContent-Type: image/jpeg\r\nContent-Length: '+str(len(jpg)).encode()+b'\r\n\r\n'+jpg+b'\r\n'
            time.sleep(0.10)
    return Response(frames(), mimetype='multipart/x-mixed-replace; boundary=frame', headers={'Cache-Control':'no-store'})

KEYS = {'Enter':pg.K_RETURN,'Backspace':pg.K_BACKSPACE,'Delete':pg.K_DELETE,'Escape':pg.K_ESCAPE,'Tab':pg.K_TAB,'ArrowUp':pg.K_UP,'ArrowDown':pg.K_DOWN,'ArrowLeft':pg.K_LEFT,'ArrowRight':pg.K_RIGHT,'Home':pg.K_HOME,'End':pg.K_END,'PageUp':pg.K_PAGEUP,'PageDown':pg.K_PAGEDOWN,' ':pg.K_SPACE}
def apply_input(vm, d):
    global mouse_pos, mouse_down
    typ = d['type']
    if typ in ('mouse','wheel'):
        try:
            mouse_pos = (max(0,min(WIDTH-1,int(d['x']))), max(0,min(HEIGHT-1,int(d['y']))))
        except (KeyError,TypeError,ValueError): return
        pg.mouse.set_pos(mouse_pos)
        if typ == 'wheel':
            vm.handle(pg.event.Event(pg.MOUSEWHEEL, {'x':0,'y':int(d.get('y',0))}))
        else:
            act=d.get('action')
            if act=='down': mouse_down=True; et=pg.MOUSEBUTTONDOWN
            elif act=='up': mouse_down=False; et=pg.MOUSEBUTTONUP
            else: et=pg.MOUSEMOTION
            vm.handle(pg.event.Event(et,{'pos':mouse_pos,'button':1,'buttons':(int(mouse_down),0,0),'rel':(0,0)}))
    elif typ == 'text':
        txt=d.get('text','')
        if isinstance(txt,str) and len(txt)==1 and txt.isprintable():
            vm.handle(pg.event.Event(pg.TEXTINPUT,{'text':txt}))
    elif typ == 'key':
        key=d.get('key','')
        code=KEYS.get(key, ord(key.lower()) if isinstance(key,str) and len(key)==1 and key.lower() in 'abcdefghijklmnopqrstuvwxyz0123456789' else pg.K_UNKNOWN)
        if code==pg.K_UNKNOWN: return
        mod=(pg.KMOD_CTRL if d.get('ctrl') else 0)|(pg.KMOD_SHIFT if d.get('shift') else 0)|(pg.KMOD_ALT if d.get('alt') else 0)
        pg.key.set_mods(mod)
        vm.handle(pg.event.Event(pg.KEYDOWN if d.get('action')=='down' else pg.KEYUP,{'key':code,'mod':mod,'unicode':key if len(key)==1 else ''}))

def vm_loop():
    global latest_frame
    vm=pyvm.VM()
    pyvm.W,pyvm.H=WIDTH,HEIGHT
    vm.scr=pg.display.set_mode((WIDTH,HEIGHT))
    vm.wall=vm.make_wallpaper()
    clock=pg.time.Clock()
    while True:
        dt=clock.tick(12)/1000
        pg.event.pump()
        for _ in range(100):
            try: apply_input(vm,commands.get_nowait())
            except queue.Empty: break
            except Exception as ex: print('Input error:',ex,flush=True)
        if vm.boot<3.0:
            vm.boot+=dt
            if vm.boot>=3.0 and not vm.windows: vm.open('terminal')
        for w in list(vm.windows): w.app.update(dt)
        vm.draw()
        # JPEG frames are smaller and faster than PNG for this prototype.
        raw=pg.image.tostring(vm.scr,'RGB')
        image=Image.frombytes('RGB',(WIDTH,HEIGHT),raw)
        buf=io.BytesIO(); image.save(buf,format='JPEG',quality=65)
        with frame_lock: latest_frame=buf.getvalue()

if __name__=='__main__':
    threading.Thread(target=lambda: app.run(host='0.0.0.0',port=int(os.environ.get('PORT','5000')),threaded=True,use_reloader=False),daemon=True).start()
    vm_loop()
