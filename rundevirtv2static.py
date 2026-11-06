import sys
import devirtv2statictable as st
import devirtv2staticexec as ex
import devirtv2extract as extr

def main(inpath, outdir, outlua):
    infodata = extr.extract(inpath, outdir)
    pname = infodata["dispatcher"]
    info = ex.extractinfo(inpath, pname)
    proto = infodata["proto"]
    code = ex.compileprotobody(info, proto)
    preamble = info.get("modulepreamble") or []
    if preamble:
        code = "\n".join(preamble) + "\n" + code
                                                                  
    code = ex.deadcodeafterreturn(code)
    with open(outlua, "w") as f:
        f.write(code)
    print("wrote", outlua, "length", len(code))
    fb = info.get("cfgfallbacks") or []
    if fb:
                                                                           
        print("WARNING: %d proto(s) fell back to the CFG emitter" % len(fb))
        for e in fb[:5]:
            print("   protoid", e["protoid"], "->", e["reason"])
        if len(fb) > 5:
            print("   ... and %d more" % (len(fb) - 5))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3])
