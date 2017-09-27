#!/usr/bin/env python3

"""Fuzz the F* interactive REPL.

This script generates random sequences of F* REPL queries, feeds them to F*, and
prints the resulting transcripts.

Typical invocation::

   # Run 500 queries from tutorial.fst; save results to '500.master'
   $ ./fuzz.py tutorial.fst --nqueries 500 --seed 0 > 500.master

   # Run 500 queries with a different F*; save results to '500.staging'
   $ ./fuzz.py tutorial.fst --nqueries 500 --seed 0 \
        --fstar /build/fstar/staging/bin/fstar.exe > 500.staging

   # Compare outputs
   $ diff 500.master 500.staging
"""

import argparse
import random
import io
import json
import subprocess
import sys

from pprint import pprint

import cleanup

DEBUG = False
def debug(fmt, *args, **kwargs):
    if DEBUG:
        kwargs.update({"file": sys.stderr, "flush": True})
        print(fmt.format(*args) if args != "" else fmt, **kwargs)

def fstar_ide_cli(fstar_exe, fname):
    return [fstar_exe, "--ide", fname]

class Decl(object):
    def __init__(self, lines, beg, end):
        begl, begc = beg
        endl, endc = end

        self.line = begl
        self.column = begc

        begl, endl = begl - 1, endl - 1
        if begl == endl:
            self.lines = [lines[begl][begc:endc]]
        else:
            self.lines = []
            self.lines.append(lines[begl][begc:])
            self.lines.extend(lines[begl + 1:endl])
            self.lines.append(lines[endl][:endc])

        self.code = "\n".join(self.lines)

    def __repr__(self):
        return "Decl(l={}, c={}, code={})".format(self.line, self.column, repr(self.code))

    # @classmethod
    # def from_json(cls, lines, js):
    #     return cls(lines, begl)

def segment_using_ranges(lines, ranges):
    prev_end = [1, 0]
    for rng in ranges:
        end = rng["end"]
        yield Decl(lines, prev_end, end)
        prev_end = end

def segment(fstar_exe, fname):
    with open(fname, encoding="utf-8") as f:
        code = f.read()
    qsegment = {"query-id": "1", "query": "segment", "args": {"code": code}}

    input = json.dumps(qsegment).encode("utf-8")
    output = subprocess.check_output(fstar_ide_cli(fstar_exe, fname), input=input)
    response = json.loads(output.decode("utf-8").splitlines()[-1])
    if response["status"] != "success":
        raise Exception("Unexpected status {}".format(response["status"]))
    ranges = [decl["def_range"] for decl in response["response"]["decls"]]

    lines = code.splitlines()
    py_decls = list(segment_using_ranges(lines, ranges))
    return py_decls

QUERY_KINDS = ["push", "pop", "peek"]
DECL_ID_DELTA = {"push": 1, "peek": 0, "pop": -1}

def make_queries(decls, nqueries=50, seed=None):
    rnd = random.Random(seed)

    qid = 0
    next_decl_id = 0
    while qid < nqueries:
        kind = rnd.choice(QUERY_KINDS)
        if kind == "push" or kind == "peek":
            if next_decl_id >= len(decls):
                continue
            decl = decls[next_decl_id]
            args = {"kind": "lax", "code": decl.code, "line": decl.line, "column": decl.column}
        if kind == "pop":
            if next_decl_id <= 0:
                continue
            args = {}
        qid += 1
        next_decl_id += DECL_ID_DELTA[kind]
        yield {"query-id": str(qid), "query": kind, "args": args}

        if qid % 100 == 0:
            debug("{} / {}", qid, nqueries, end="\r")

def run(fstar_exe, fname, queries):
    process = subprocess.Popen(fstar_ide_cli(fstar_exe, fname),
                               stdin=subprocess.PIPE,
                               stdout=subprocess.PIPE)

    pstdin = io.TextIOWrapper(process.stdin, "utf-8")
    pstdout = io.TextIOWrapper(process.stdout, "utf-8")

    repl_info = pstdout.readline()
    # print("<<< {}".format(repl_info))

    for query in queries:
        in_line = json.dumps(query, sort_keys=True)
        print(">>> {}".format(in_line), flush=True)
        pstdin.write(in_line + "\n")
        pstdin.flush()
        out_line = pstdout.readline()
        print("<<< {}".format(cleanup.cleanup_one(out_line)), flush=True)
        yield json.loads(out_line)

    pstdin.close()
    process.wait()

def parse_arguments():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--seed", type=int, default=None,
                        help="Random seed to use for this run.")
    parser.add_argument("--nqueries", type=int, default=50,
                        help="Number of queries to run (default: %(default)s).")
    parser.add_argument("--fstar-parser", default="../../../bin/fstar.exe",
                        help=("F* binary used to segment 'source_file' " +
                              "(default: %(default)s)."))
    parser.add_argument("--fstar", default=None,
                        help="F* executable to test (default: FSTAR_PARSER).")
    parser.add_argument("--progress", action="store_true", default=False,
                        help="Print progress messages (default: run silently).")
    parser.add_argument("source_file",
                        help="F* file to read code from.")
    return parser.parse_args()

def main():
    global DEBUG
    args = parse_arguments()

    DEBUG = args.progress
    debug("Segmenting {}...", args.source_file)
    decls = segment(args.fstar_parser, args.source_file)
    debug("Running {} queries...", args.nqueries)
    queries = make_queries(decls, args.nqueries, args.seed)
    list(run(args.fstar or args.fstar_parser, args.source_file, queries))
    debug("Done.")

if __name__ == '__main__':
    main()
