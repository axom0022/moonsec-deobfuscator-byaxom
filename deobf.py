import os
import shutil
import sys
import tempfile
import webapp


def main():
    if len(sys.argv) < 2 or len(sys.argv) > 3:
        sys.stderr.write("usage: python3 deobf.py <input.lua> [output.lua]\n")
        sys.exit(1)

    inpath = os.path.abspath(sys.argv[1])
    if not os.path.isfile(inpath):
        sys.stderr.write("file not found: %s\n" % inpath)
        sys.exit(1)

    if len(sys.argv) == 3:
        outpath = sys.argv[2]
    else:
        base, _ = os.path.splitext(sys.argv[1])
        outpath = base + ".deobf.lua"

    raw = open(inpath, encoding="utf-8", errors="replace").read()
    ver = webapp.detect(raw) or "v2"

    workdir = tempfile.mkdtemp(prefix="moonsec_cli_")
    try:
        src = os.path.join(workdir, "input.lua")
        shutil.copy2(inpath, src)
        if ver == "v3":
            code, stats, err = webapp.run_v3(src, workdir)
        else:
            code, stats, err = webapp.run_v2(src, workdir)
        if err or code is None:
            sys.stderr.write((err or "deobfuscation failed") + "\n")
            sys.exit(1)
        open(outpath, "w", encoding="utf-8").write(code)
        print("wrote %s (%s, %d bytes)" % (outpath, ver.upper(), len(code)))
    finally:
        shutil.rmtree(workdir, ignore_errors=True)


if __name__ == "__main__":
    main()
