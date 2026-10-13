#!/usr/bin/env python3
"""Times the benchmark executables that the Makefile builds, for each
backend, and prints a markdown table: the median wall-clock time of --runs
runs, and the peak resident set size."""
import argparse, os, resource, statistics, subprocess, sys, tempfile, time

# Cherry with another malloc: [cherry+NAME] runs the Cherry executable with
# the library given by --preload NAME=PATH in LD_PRELOAD.
PRELOADS = {}

def command(outdir, backend, bench):
    if "+" in backend:
        base, alloc = backend.split("+", 1)
        return ["env", "LD_PRELOAD=" + PRELOADS[alloc]] + command(outdir, base, bench)
    if backend == "cherry":
        return [os.path.join(outdir, "cherry", bench + ".exe")]
    if backend == "ocaml":
        return [os.path.join(outdir, "ocaml", bench + ".exe")]
    if backend == "fsharp":
        return ["dotnet", os.path.join(outdir, "fs", bench, "bin", "Release",
                                       "net10.0", bench + ".dll")]
    raise ValueError(backend)

STACK = 1 << 30

def big_stack():
    """Every backend gets a 1 GB stack, OCaml 5's default limit: the
    benchmarks recurse deeply where they are not tail calls, and the C and
    .NET defaults of 8 MB are not enough for all of them."""
    resource.setrlimit(resource.RLIMIT_STACK, (STACK, STACK))

def run_once(cmd):
    """Wall time in seconds, peak RSS in MB, exit status.  The RSS comes from
    GNU time rather than from our own wait4: a child forked from Python
    starts out with Python's resident set, which ru_maxrss would count."""
    with tempfile.NamedTemporaryFile(mode="r") as f:
        t0 = time.perf_counter()
        rc = subprocess.call(["/usr/bin/time", "-q", "-f", "%M", "-o", f.name] + cmd,
                             stdout=subprocess.DEVNULL, preexec_fn=big_stack)
        t = time.perf_counter() - t0
        lines = f.read().split()
        rss = int(lines[-1]) / 1024.0 if lines else 0.0
    return t, rss, rc

NAMES = {"cherry": "Cherry", "ocaml": "OCaml", "fsharp": "F#"}

def name(be):
    if "+" in be:
        base, alloc = be.split("+", 1)
        return f"{NAMES[base]} ({alloc})"
    return NAMES[be]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--outdir", default="_output")
    ap.add_argument("--backends", default="cherry,ocaml,fsharp",
                    help="comma-separated: cherry, ocaml, fsharp, or cherry+NAME")
    ap.add_argument("--preload", action="append", default=[], metavar="NAME=PATH",
                    help="a malloc library for the cherry+NAME backend")
    ap.add_argument("--baseline", default="ocaml",
                    help="the backend the other times are given as ratios to")
    ap.add_argument("benches", nargs="+")
    a = ap.parse_args()
    a.backends = [be for be in a.backends.split(",") if be]
    for pl in a.preload:
        n, path = pl.split("=", 1)
        PRELOADS[n] = path
    failed = False
    rows = []
    for b in a.benches:
        row = {}
        for be in a.backends:
            cmd = command(a.outdir, be, b)
            ts, rss = [], 0.0
            for _ in range(a.runs):
                t, m, rc = run_once(cmd)
                if rc != 0:
                    print(f"{b} ({be}): exit status {rc}", file=sys.stderr)
                    failed = True
                    break
                ts.append(t)
                rss = max(rss, m)
            row[be] = (statistics.median(ts), rss) if ts and len(ts) == a.runs else None
            print(f"  {b} {be}: " + (f"{row[be][0]:.3f} s, {row[be][1]:.0f} MB" if row[be] else "FAILED"),
                  file=sys.stderr)
        rows.append((b, row))
    base = a.baseline if a.baseline in a.backends else a.backends[0]
    print(f"Median wall-clock time of {a.runs} runs in seconds, with the ratio to "
          f"{name(base)} (lower is faster); peak RSS in MB.\n")
    hdr = ["Benchmark"] + [f"{name(be)} (s)" for be in a.backends] \
        + [f"{name(be)} RSS" for be in a.backends]
    print("| " + " | ".join(hdr) + " |")
    print("|" + "|".join(["---"] + ["---:"] * (len(hdr) - 1)) + "|")
    for b, row in rows:
        cells = [b.removeprefix("Bench")]
        for be in a.backends:
            if not row[be]:
                cells.append("fail")
            elif be == base or not row[base]:
                cells.append(f"{row[be][0]:.3f}")
            else:
                cells.append(f"{row[be][0]:.3f} ({row[be][0] / row[base][0]:.2f}x)")
        cells += [f"{row[be][1]:.0f}" if row[be] else "-" for be in a.backends]
        print("| " + " | ".join(cells) + " |")
    sys.exit(1 if failed else 0)

if __name__ == "__main__":
    main()
