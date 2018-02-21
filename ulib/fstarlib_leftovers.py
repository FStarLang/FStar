#!/usr/bin/env python
"""
List fstarlib files not included in the compiler.

We need this to compile a clean version of fstar-tactics-lib, containing no
duplicate copies of modules included in the compiler.
"""
import os
import sys

def libs(marker, exts):
    for folder in sys.argv[1:]:
        if folder.startswith(marker):
            folder = folder[len(marker):]
            for fname in os.listdir(folder):
                name, ext = os.path.splitext(fname)
                if ext in exts:
                    yield (name, os.path.join(folder, fname))

def main():
    excluded = set(name for name, _ in libs("-", [".cmi"]))
    for name, path in libs("+", [".ml"]):
        if name not in excluded:
            print(path)

main()
