import hashlib
import os
import pickle
import sys

from luaparser import ast as L

try:
    from importlib.metadata import version as _ver
    _LPVER = _ver("luaparser")
except Exception:
    _LPVER = "unknown"

CACHE_DIR = os.path.join(os.path.expanduser("~"), ".cache", "moonsec-ast")


def parse(src):
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 100000))
    key = hashlib.sha256((_LPVER + "\0" + src).encode("utf-8", "surrogatepass")).hexdigest()
    path = os.path.join(CACHE_DIR, key + ".pkl")
    if os.path.exists(path):
        try:
            with open(path, "rb") as f:
                return pickle.load(f)
        except Exception:
            pass
    tree = L.parse(src)
    try:
        os.makedirs(CACHE_DIR, exist_ok=True)
        tmp = path + ".tmp%d" % os.getpid()
        with open(tmp, "wb") as f:
            pickle.dump(tree, f, protocol=pickle.HIGHEST_PROTOCOL)
        os.replace(tmp, path)
    except Exception:
        pass
    return tree
