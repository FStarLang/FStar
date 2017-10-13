#!/usr/bin/env python2

"""Cleanup interactive transcript received on standard input.

This mostly consists in pretty-pretting JSON messages and sorting their
fields, to permit text-based comparisons against reference transcripts.

Usage: python2 cleanup.py fname.clean < fname.dirty
"""

import json
import sys
import re

def cleanup_json(js):
    if isinstance(js, dict):
        if "fname" in js:
            js["fname"] = js["fname"].replace('\\', '/')
        for v in js.itervalues():
            cleanup_json(v)
    elif isinstance(js, list):
        for v in js:
            cleanup_json(v)

def cleanup_one(line):
    line = re.sub(r"\b(?<![\\])u[0-9][0-9]+\b", "u[...]", line)
    try:
        js = json.loads(line)
        if js.get("kind") == "protocol-info":
            js = {"kind": "[...]"} # Drop entire message
        cleanup_json(js)
        return json.dumps(js, ensure_ascii=False, sort_keys=True) + "\n"
    except Exception as ex:
        return line

def main():
    # Writing to stdout converts newlines, which confuses diff on Windows, so
    # write to a file instead.  There's no reasonable way to do this in a Python
    # 2/3 compatible way, so the following is Python-2 only.
    lines = [line.decode("utf-8") for line in sys.stdin]
    with open(sys.argv[1], mode="wb") as out:
        for line in lines:
            out.write(cleanup_one(line).encode("utf-8"))
            out.flush()

if __name__ == '__main__':
    main()
