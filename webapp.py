import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time

from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import unquote

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.environ.get("LUAU_TOOLS", "/home/user/tools")

_pipelock = threading.Lock()

V2_TIMEOUT = 600
V3_TIMEOUT = 180


def detect(src):
    head = src[:200000]
    if "MoonSec V3" in head or "_ZSWmDsaqpxPR" in head or "_KRbtOqVmJMLG" in head:
        return "v3"
    if "Protected_by_MoonSecV2" in head:
        return "v2"
    if "discord.gg/gQEH2uZxUk" in head:
        return "v2"
    if "MoonSec" in head:
        return "v2"
    return None


SAMPLEDIR = os.path.join(HERE, "samples") if os.path.isdir(os.path.join(HERE, "samples")) else "/home/user/uploads"

SAMPLES = [
    ("example",        "Example.txt",          "Example"),
    ("example7",       "Example#7.txt",        "Example #7"),
    ("example9",       "Example#9.txt",        "Example #9"),
    ("example10",      "Example#10.txt",       "Example #10"),
    ("boxing-battles", "BoxingBattles.txt",    "Boxing Battles"),
    ("anti-afk",       "Anti AFK MoonSec.txt", "Anti AFK"),
]
SAMPLEBYID = {s[0]: s for s in SAMPLES}


def list_samples():
    out = []
    for sid, fname, label in SAMPLES:
        p = os.path.join(SAMPLEDIR, fname)
        if not os.path.exists(p):
            continue
        try:
            head = open(p, encoding="utf-8", errors="replace").read(200000)
            ver = detect(head) or "?"
        except Exception:
            continue
        out.append({"id": sid, "label": label, "filename": fname,
                    "version": ver, "bytes": os.path.getsize(p)})
    return out


def load_sample(sid):
    if sid not in SAMPLEBYID:
        return {"ok": False, "error": "unknown sample"}
    sid, fname, label = SAMPLEBYID[sid]
    p = os.path.join(SAMPLEDIR, fname)
    if not os.path.exists(p):
        return {"ok": False, "error": "sample file missing"}
    try:
        return {"ok": True, "filename": fname,
                "text": open(p, encoding="utf-8", errors="replace").read()}
    except Exception as e:
        return {"ok": False, "error": str(e)}


def _run(cmd, timeout, cwd=HERE):
    return subprocess.run(
        cmd, cwd=cwd, timeout=timeout,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, errors="replace",
    )


def run_v2(srcpath, workdir):
    import shutil
    import uuid
    slug = "web_" + uuid.uuid4().hex[:8]
    r = _run(["bash", "rebuild.sh", srcpath, slug], V2_TIMEOUT)
    out = os.path.join(HERE, slug + ".deobf.txt")
    try:
        if not os.path.exists(out):
            lines = (r.stdout or "").strip().splitlines()
            err = [l for l in lines if "Error" in l or "error" in l or "exceeded" in l]
            detail = (err[-1] if err else "\n".join(lines[-4:])).strip()
            return None, {}, ("V2 pipeline stopped: " + detail +
                               "\n(Known blocker: irreducible dispatch loops, see v2reimpl-notes.md)")
        code = open(out, encoding="utf-8", errors="replace").read()
    finally:
        if os.path.exists(out):
            os.remove(out)
        shutil.rmtree("/tmp/rb_" + slug, ignore_errors=True)
    stats = {"bytes": len(code), "lines": code.count("\n") + 1, "warnings": []}
    return code, stats, None


V3_STEPS = 15_000_000


def _tidy(text):
    return "\n".join(l for l in text.split("\n") if l.strip() != ";")


def run_v3(srcpath, workdir):
    import glob
    prefix = os.path.join(workdir, "vm")
    events = os.path.join(workdir, "events.json")
    r = _run([sys.executable, "v3vmtrace.py", srcpath, str(V3_STEPS), "--wm",
              "--out=" + prefix, "--events=" + events], V3_TIMEOUT)
    log = r.stdout or ""
    payloads = sorted(p for p in glob.glob(prefix + ".payload*.lua")
                      if re.fullmatch(re.escape(prefix) + r"\.payload\d+\.lua", p))

    if payloads:
        parts = []
        for p in payloads:
            restyled = p + ".restyled.lua"
            _run([sys.executable, "optimizeast.py", p, restyled], V3_TIMEOUT)
            final = p + ".final.lua"
            if os.path.exists(restyled):
                _run([sys.executable, "postprocessv2.py", restyled, final], V3_TIMEOUT)
            src = final if os.path.exists(final) else p
            parts.append(_tidy(open(src, encoding="latin-1", errors="replace").read()).strip())
        code = "\n\n".join(parts) + "\n"
        stats = {"bytes": len(code), "payloads": len(payloads), "partial": False, "warnings": []}
        return code, stats, None

    gen = os.path.join(workdir, "vm.emit.lua")
    if os.path.exists(events):
        _run([sys.executable, "v3emit.py", events, gen], V3_TIMEOUT)
    if os.path.exists(gen):
        final = gen + ".final.lua"
        _run([sys.executable, "postprocessv2.py", gen, final], V3_TIMEOUT)
        src = final if os.path.exists(final) else gen
        code = open(src, encoding="utf-8", errors="replace").read()
        stats = {"bytes": len(code), "payloads": 0, "partial": True,
                 "warnings": ["no payload loaded by the VM; generated from the VM event log (partial)"]}
        return code, stats, None
    return None, {}, "V3 pipeline failed: no payload loaded and event log unavailable"


def _q(s):
    return '"' + (s.replace("\\", "\\\\").replace('"', '\\"')
                   .replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t")) + '"'


def parsecheck(path):
    exe = os.path.join(TOOLS, "luau-ast")
    if not os.path.exists(exe):
        return None
    try:
        r = _run([exe, path], 60)
        return "PARSE OK" if r.returncode == 0 else "PARSE FAIL"
    except Exception:
        return None


PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>MoonSec Deobfuscator</title>
<style>
  :root{
    --bg:#0d1117; --panel:#161b22; --panel2:#1c2230; --line:#2a3140;
    --fg:#e6edf3; --dim:#8b96a5; --accent:#4c8dff; --accent2:#3fb950;
    --warn:#d29922; --err:#f85149;
  }
  *{box-sizing:border-box}
  html,body{height:100%}
  body{
    margin:0; background:var(--bg); color:var(--fg);
    font:14px/1.5 ui-sans-serif,system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;
  }
  .wrap{max-width:1400px;margin:0 auto;padding:22px 20px 40px;display:flex;flex-direction:column;height:100vh}
  header{display:flex;align-items:baseline;gap:14px;flex-wrap:wrap;margin-bottom:16px}
  h1{font-size:19px;margin:0;letter-spacing:.2px}
  .sub{color:var(--dim);font-size:12.5px}
  .grid{display:grid;grid-template-columns:1fr 1fr;gap:16px;flex:1;min-height:0}
  @media(max-width:900px){.grid{grid-template-columns:1fr}.wrap{height:auto}}
  .panel{background:var(--panel);border:1px solid var(--line);border-radius:10px;display:flex;flex-direction:column;min-height:0;overflow:hidden}
  .phead{display:flex;align-items:center;justify-content:space-between;gap:10px;
    padding:9px 13px;border-bottom:1px solid var(--line);background:var(--panel2);flex:0 0 auto}
  .phead h2{font-size:12px;margin:0;text-transform:uppercase;letter-spacing:.9px;color:var(--dim);font-weight:600}
  .phead .meta{font-size:11.5px;color:var(--dim);font-variant-numeric:tabular-nums}
  textarea{
    flex:1;width:100%;min-height:260px;resize:none;border:0;outline:none;
    background:#0b1017;color:var(--fg);padding:13px;
    font:12.5px/1.55 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
    tab-size:2;white-space:pre;overflow:auto;
  }
  textarea::placeholder{color:#5a6472}
  .drop{margin:11px 13px 0;padding:16px;border:1.5px dashed var(--line);border-radius:8px;
    text-align:center;color:var(--dim);font-size:12.5px;cursor:pointer;transition:.15s;background:#0b1017}
  .drop:hover,.drop.over{border-color:var(--accent);color:var(--fg);background:#101827}
  .drop b{color:var(--accent)}
  .bar{display:flex;align-items:center;gap:9px;padding:11px 13px;border-top:1px solid var(--line);flex:0 0 auto;flex-wrap:wrap}
  button{
    font:600 13px ui-sans-serif,system-ui,sans-serif;padding:8px 17px;border-radius:7px;
    border:1px solid var(--line);background:var(--panel2);color:var(--fg);cursor:pointer;transition:.13s;
  }
  button:hover:not(:disabled){border-color:#3d4759;background:#222b3a}
  button:disabled{opacity:.45;cursor:not-allowed}
  .primary{background:var(--accent);border-color:var(--accent);color:#fff}
  .primary:hover:not(:disabled){background:#3d7ef5;border-color:#3d7ef5}
  .ghost{padding:6px 13px;font-size:12px}
  select{
    font:600 12px ui-sans-serif,system-ui,sans-serif;padding:7px 11px;border-radius:7px;
    border:1px solid var(--line);background:var(--panel2);color:var(--fg);cursor:pointer;
    max-width:190px;
  }
  select:hover{border-color:#3d4759;background:#222b3a}
  .spacer{flex:1}
  .status{
    padding:9px 13px;font-size:12.5px;border-top:1px solid var(--line);
    color:var(--dim);display:flex;align-items:center;gap:8px;flex:0 0 auto;min-height:36px
  }
  .dot{width:8px;height:8px;border-radius:50%;background:#3d4759;flex:0 0 auto}
  .dot.run{background:var(--warn);animation:pulse 1s infinite}
  .dot.ok{background:var(--accent2)}
  .dot.bad{background:var(--err)}
  @keyframes pulse{50%{opacity:.35}}
  .spinner{width:13px;height:13px;border:2px solid #2a3140;border-top-color:var(--accent);
    border-radius:50%;animation:spin .7s linear infinite;display:none}
  @keyframes spin{to{transform:rotate(360deg)}}
  .spinner.on{display:inline-block}
  .fname{font-size:11.5px;color:var(--dim);overflow:hidden;text-overflow:ellipsis;white-space:nowrap;max-width:200px}
  .tag{font-size:10.5px;padding:2px 7px;border-radius:20px;border:1px solid var(--line);color:var(--dim)}
  .tag.v2{color:#79c0ff;border-color:#1f4b8f;background:#0d2137}
  .tag.v3{color:#d2a8ff;border-color:#5a3d82;background:#1c1230}
  .tag.ok{color:var(--accent2);border-color:#1f6f37;background:#0d2818}
  .tag.bad{color:var(--err);border-color:#8f2222;background:#2d1212}
  .warnbox{padding:8px 13px;font-size:11.5px;color:var(--warn);background:#1d1707;
    border-top:1px solid var(--line);max-height:88px;overflow:auto;display:none;
    font-family:ui-monospace,monospace;white-space:pre-wrap}
  .warnbox.on{display:block}
  input[type=file]{display:none}
  .hint{font-size:11px;color:#5a6472;padding:0 13px 11px}
</style>
</head>
<body>
<div class="wrap">
  <header>
    <h1>MoonSec Deobfuscator</h1>
    <span class="sub">static devirtualizer &middot; MoonSec V2 full source &middot; V3 constant pool</span>
  </header>

  <div class="grid">
    <section class="panel">
      <div class="phead">
        <h2>Input</h2>
        <span class="meta" id="insize"></span>
      </div>
      <div class="drop" id="drop">
        <b>Choose file</b> or drop here &nbsp;&middot;&nbsp; or paste Lua below
      </div>
      <input type="file" id="file" accept=".lua,.txt,.luau,text/*">
      <textarea id="in" spellcheck="false" placeholder="paste obfuscated Lua here..."></textarea>
      <div class="bar">
        <button class="primary" id="go">Deobfuscate</button>
        <select id="sample" title="load a bundled sample"></select>
        <button class="ghost" id="clear">Clear</button>
        <span class="spacer"></span>
        <span class="fname" id="fname"></span>
      </div>
      <div class="hint" id="detect"></div>
    </section>

    <section class="panel">
      <div class="phead">
        <h2>Output</h2>
        <span class="meta" id="outmeta"></span>
      </div>
      <textarea id="out" spellcheck="false" readonly placeholder="deobfuscated output appears here..."></textarea>
      <div class="warnbox" id="warnbox"></div>
      <div class="bar">
        <button id="copy">Copy</button>
        <button id="download">Download .txt</button>
        <span class="spacer"></span>
        <span class="tag" id="parsetag" style="display:none"></span>
      </div>
      <div class="status">
        <span class="dot" id="dot"></span>
        <span class="spinner" id="spin"></span>
        <span id="msg">Idle.</span>
      </div>
    </section>
  </div>
</div>

<script>
var $ = function(id){ return document.getElementById(id); };
var inEl=$('in'), outEl=$('out'), fileEl=$('file'), dropEl=$('drop');
var goBtn=$('go'), copyBtn=$('copy'), dlBtn=$('download');
var dot=$('dot'), spin=$('spin'), msg=$('msg');

var sampleSel = $('sample');

function setStatus(text, kind){
  msg.textContent = text;
  dot.className = 'dot' + (kind ? ' ' + kind : '');
  spin.className = 'spinner' + (kind === 'run' ? ' on' : '');
}
function busy(on){
  goBtn.disabled = on; copyBtn.disabled = on; dlBtn.disabled = on;
  if (on) setStatus('Running pipeline...', 'run');
}

function fmtBytes(n){
  if (n < 1024) return n + ' B';
  if (n < 1048576) return (n/1024).toFixed(1) + ' KB';
  return (n/1048576).toFixed(2) + ' MB';
}

inEl.addEventListener('input', function(){
  var v = inEl.value;
  $('insize').textContent = v ? fmtBytes(v.length) + ' / ' + v.split('\n').length + ' lines' : '';
  var d = detectVersion(v);
  $('detect').innerHTML = d
    ? '<span class="tag ' + d + '">detected: MoonSec ' + d.toUpperCase() + '</span>'
    : (v ? '<span style="color:#5a6472">no MoonSec signature detected yet</span>' : '');
});

function detectVersion(v){
  if (!v) return null;
  if (v.indexOf('MoonSec V3') >= 0) return 'v3';
  if (v.indexOf('Protected_by_MoonSecV2') >= 0) return 'v2';
  if (v.indexOf('discord.gg/gQEH2uZxUk') >= 0) return 'v2';
  return null;
}

dropEl.addEventListener('click', function(){ fileEl.click(); });
dropEl.addEventListener('dragover', function(e){ e.preventDefault(); dropEl.classList.add('over'); });
dropEl.addEventListener('dragleave', function(){ dropEl.classList.remove('over'); });
dropEl.addEventListener('drop', function(e){
  e.preventDefault(); dropEl.classList.remove('over');
  if (e.dataTransfer.files.length) loadFile(e.dataTransfer.files[0]);
});
fileEl.addEventListener('change', function(){
  if (fileEl.files.length) loadFile(fileEl.files[0]);
});

function loadFile(f){
  var fr = new FileReader();
  fr.onload = function(){
    inEl.value = fr.result;
    $('fname').textContent = f.name + ' (' + fmtBytes(f.size) + ')';
    inEl.dispatchEvent(new Event('input'));
    setStatus('Loaded ' + f.name + '. Press Deobfuscate.', null);
  };
  fr.readAsText(f);
}

$('clear').addEventListener('click', function(){
  inEl.value = ''; outEl.value = ''; fileEl.value = '';
  $('fname').textContent = ''; $('insize').textContent = '';
  $('outmeta').textContent = ''; $('detect').innerHTML = '';
  $('warnbox').className = 'warnbox'; $('warnbox').textContent = '';
  $('parsetag').style.display = 'none';
  setStatus('Idle.', null);
});

(function loadSamples(){
  var o = document.createElement('option');
  o.textContent = 'Load sample...'; o.value = '';
  sampleSel.appendChild(o);
  fetch('api/samples').then(function(r){ return r.json(); }).then(function(list){
    list.forEach(function(s){
      var opt = document.createElement('option');
      opt.value = s.id;
      opt.textContent = s.label + '  (' + s.version.toUpperCase() + ')';
      sampleSel.appendChild(opt);
    });
  }).catch(function(){
    var opt = document.createElement('option');
    opt.textContent = 'no samples'; sampleSel.appendChild(opt);
  });
})();

sampleSel.addEventListener('change', function(){
  var id = sampleSel.value;
  if (!id) return;
  setStatus('Loading sample...', 'run');
  fetch('api/sample/' + encodeURIComponent(id)).then(function(r){ return r.json(); }).then(function(j){
    if (!j.ok){ setStatus('Could not load sample: ' + j.error, 'bad'); return; }
    inEl.value = j.text;
    $('fname').textContent = j.filename;
    inEl.dispatchEvent(new Event('input'));
    setStatus('Loaded ' + j.filename + ' - press Deobfuscate.', null);
    sampleSel.value = '';
  }).catch(function(e){ setStatus('Sample load failed: ' + e.message, 'bad'); });
});

goBtn.addEventListener('click', function(){
  var src = inEl.value;
  if (!src.trim()){ setStatus('Nothing to deobfuscate - paste code or upload a file.', 'bad'); return; }
  busy(true);
  $('parsetag').style.display = 'none';
  $('warnbox').className = 'warnbox';

  var t0 = Date.now();
  fetch('api/deobfuscate', {
    method: 'POST',
    headers: {'Content-Type': 'application/json'},
    body: JSON.stringify({text: src, filename: $('fname').textContent || 'input.lua'})
  }).then(function(r){
    return r.json().catch(function(){ return {ok:false, error:'server returned non-JSON (HTTP ' + r.status + ')'}; });
  }).then(function(j){
    busy(false);
    var secs = ((Date.now() - t0) / 1000).toFixed(1);
    if (!j.ok){
      setStatus('Failed: ' + (j.error || 'unknown error'), 'bad');
      outEl.value = j.error || '';
      return;
    }
    outEl.value = j.output;
    $('outmeta').textContent = fmtBytes(j.output.length) + ' / '
      + j.output.split('\n').length + ' lines / ' + secs + 's';
    var w = (j.warnings && j.warnings.length) ? j.warnings : [];
    if (w.length){
      $('warnbox').className = 'warnbox on';
      $('warnbox').textContent = w.join('\n');
    }
    if (j.parse){
      var t = $('parsetag');
      t.style.display = ''; t.textContent = j.parse;
      t.className = 'tag ' + (j.parse === 'PARSE OK' ? 'ok' : 'bad');
    }
    setStatus('Done - MoonSec ' + j.version.toUpperCase()
      + (j.stats && j.stats.strings ? ' (' + j.stats.strings + ' strings recovered)' : '')
      + ' in ' + secs + 's', 'ok');
  }).catch(function(e){
    busy(false);
    setStatus('Request failed: ' + e.message, 'bad');
  });
});

copyBtn.addEventListener('click', function(){
  if (!outEl.value){ setStatus('Nothing to copy.', 'bad'); return; }
  var ok = false;
  if (navigator.clipboard && navigator.clipboard.writeText){
    navigator.clipboard.writeText(outEl.value).then(function(){
      flash('Copied to clipboard.', 'ok');
    }).catch(function(){ ok = legacyCopy(); });
  } else {
    ok = legacyCopy();
  }
  function legacyCopy(){
    outEl.removeAttribute('readonly'); outEl.select(); outEl.setSelectionRange(0, 999999);
    try {
      var r = document.execCommand('copy');
      outEl.setAttribute('readonly', 'readonly');
      window.getSelection().removeAllRanges();
      flash(r ? 'Copied to clipboard.' : 'Copy failed - select and press Ctrl+C.', r ? 'ok' : 'bad');
      return r;
    } catch(e){
      outEl.setAttribute('readonly','readonly');
      flash('Copy failed - select and press Ctrl+C.', 'bad');
      return false;
    }
  }
});

var flasht = null;
function flash(text, kind){
  setStatus(text, kind);
  clearTimeout(flasht);
  flasht = setTimeout(function(){
    var t = $('parsetag');
    if (t.textContent === 'PARSE OK') setStatus('Done.', 'ok');
    else setStatus('Idle.', null);
  }, 2600);
}

dlBtn.addEventListener('click', function(){
  if (!outEl.value){ setStatus('Nothing to download.', 'bad'); return; }
  var blob = new Blob([outEl.value], {type: 'text/plain;charset=utf-8'});
  var url = URL.createObjectURL(blob);
  var a = document.createElement('a');
  a.href = url;
  a.download = ($('fname').textContent || 'output').replace(/\.[^.]+$/, '') + '.deobf.txt';
  document.body.appendChild(a); a.click(); document.body.removeChild(a);
  setTimeout(function(){ URL.revokeObjectURL(url); }, 1000);
  flash('Downloaded ' + a.download, 'ok');
});

document.addEventListener('keydown', function(e){
  if ((e.ctrlKey || e.metaKey) && e.key === 'Enter' && !goBtn.disabled) goBtn.click();
});
</script>
</body>
</html>
"""


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "moonsec-deob/1.0"

    def log_message(self, fmt, *args):
        sys.stderr.write("[%s] %s\n" % (time.strftime("%H:%M:%S"), fmt % args))

    def do_GET(self):
        path = unquote(self.path.split("?")[0])
        if path in ("/", "/index.html"):
            body = PAGE.encode("utf-8")
            self._send(200, "text/html; charset=utf-8", body)
        elif path == "/api/health":
            self._send(200, "application/json", b'{"ok":true}')
        elif path == "/api/samples":
            self._send(200, "application/json; charset=utf-8",
                       json.dumps(list_samples()).encode("utf-8"))
        elif path.startswith("/api/sample/"):
            sid = path[len("/api/sample/"):]
            self._send(200, "application/json; charset=utf-8",
                       json.dumps(load_sample(sid)).encode("utf-8"))
        else:
            self._send(404, "text/plain", b"not found")

    def do_POST(self):
        path = unquote(self.path.split("?")[0])
        if path != "/api/deobfuscate":
            self._send(404, "text/plain", b"not found")
            return
        try:
            n = int(self.headers.get("Content-Length") or 0)
            raw = self.rfile.read(n) if n else b""
            try:
                payload = json.loads(raw.decode("utf-8", "replace"))
            except Exception:
                payload = {}
            src = payload.get("text") or ""
            fname = payload.get("filename") or "input.lua"
            result = self._deob(src, fname)
        except Exception as e:
            import traceback
            traceback.print_exc()
            result = {"ok": False, "error": "server error: %s" % e}
        body = json.dumps(result).encode("utf-8")
        self._send(200, "application/json; charset=utf-8", body)

    def _deob(self, src, fname):
        if not src.strip():
            return {"ok": False, "error": "empty input"}

        version = detect(src)
        if version is None:
            return {"ok": False,
                    "error": "No MoonSec signature found. Expected 'MoonSec V3' or "
                             "'Protected_by_MoonSecV2' in the file, or a paste that is not Lua."}

        workdir = tempfile.mkdtemp(prefix="webdeob_")
        srcpath = os.path.join(workdir, "input.lua")
        try:
            with open(srcpath, "w", encoding="utf-8", errors="replace") as f:
                f.write(src)

            acquired = _pipelock.acquire(timeout=V2_TIMEOUT + 60)
            if not acquired:
                return {"ok": False, "error": "server busy - another job is running"}
            try:
                t0 = time.time()
                if version == "v2":
                    code, stats, err = run_v2(srcpath, workdir)
                else:
                    code, stats, err = run_v3(srcpath, workdir)
                elapsed = round(time.time() - t0, 1)
            finally:
                _pipelock.release()

            if err:
                return {"ok": False, "error": err, "version": version}

            outpath = os.path.join(workdir, "check.lua")
            with open(outpath, "w", encoding="utf-8") as f:
                f.write(code)
            status = parsecheck(outpath)

            return {
                "ok": True,
                "version": version,
                "output": code,
                "stats": stats,
                "warnings": stats.get("warnings", []),
                "parse": status,
                "seconds": elapsed,
            }
        except subprocess.TimeoutExpired:
            return {"ok": False, "error": "pipeline timed out (>%ds)" % V2_TIMEOUT,
                    "version": version}
        except Exception as e:
            import traceback
            traceback.print_exc()
            return {"ok": False, "error": "pipeline error: %s" % e, "version": version}
        finally:
            import shutil
            shutil.rmtree(workdir, ignore_errors=True)

    def _send(self, code, ctype, body):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.end_headers()
        self.wfile.write(body)

    def do_OPTIONS(self):
        self._send(204, "text/plain", b"")


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else int(os.environ.get("PORT", "8000"))
    srv = ThreadingHTTPServer(("0.0.0.0", port), Handler)
    sys.stderr.write("MoonSec deobfuscator web UI -> http://0.0.0.0:%d\n" % port)
    sys.stderr.flush()
    srv.serve_forever()


if __name__ == "__main__":
    main()
