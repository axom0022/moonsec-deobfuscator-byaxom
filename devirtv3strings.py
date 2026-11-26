import v3bootstrap


def extractstrings(path, workdir=None, timeout=None):
    try:
        blob = v3bootstrap.static_blob(path)
    except SystemExit as e:
        return None, str(e)
    except Exception as e:
        return None, "static decode failed: %s: %s" % (type(e).__name__, e)
    return [blob], None


def parsestringtable(blob):
    import v3proto
    root, _, _, _ = v3proto.parse_blob(blob)
    out = []
    for c in root.consts:
        if isinstance(c, str):
            out.append(("string", c))
        elif c is None:
            continue
        else:
            out.append(("<number>", None))
    return out


if __name__ == "__main__":
    import sys
    blobs, err = extractstrings(sys.argv[1])
    if err:
        print("ERR:", err)
        raise SystemExit(1)
    print("recovered %d blob(s) from %s" % (len(blobs), sys.argv[1]))
    for bi, b in enumerate(blobs):
        print("--- blob %d: %d bytes ---" % (bi, len(b)))
