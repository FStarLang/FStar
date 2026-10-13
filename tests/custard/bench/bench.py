#!/usr/bin/env python3
"""Times the benchmark executables that the Makefile builds, for each
backend, and prints a markdown table: the median wall-clock time of --runs
runs, and the peak resident set size."""
import argparse, os, resource, statistics, subprocess, sys, tempfile, time

def command(outdir, backend, bench):
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

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--outdir", default="_output")
    ap.add_argument("--backends", default="cherry,ocaml,fsharp",
                    help="comma-separated; the first is the baseline for the ratios")
    ap.add_argument("benches", nargs="+")
    a = ap.parse_args()
    a.backends = a.backends.split(",")
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
    base = a.backends[0]
    hdr = ["Benchmark"] + [f"{NAMES[be]} (s)" for be in a.backends] \
        + [f"{NAMES[be]}/{NAMES[base]}" for be in a.backends[1:]] \
        + [f"{NAMES[be]} RSS (MB)" for be in a.backends]
    print("| " + " | ".join(hdr) + " |")
    print("|" + "|".join(["---"] + ["---:"] * (len(hdr) - 1)) + "|")
    for b, row in rows:
        cells = [b.removeprefix("Bench")]
        cells += [f"{row[be][0]:.3f}" if row[be] else "fail" for be in a.backends]
        cells += [f"{row[be][0] / row[base][0]:.2f}x" if row[be] and row[base] else "-"
                  for be in a.backends[1:]]
        cells += [f"{row[be][1]:.0f}" if row[be] else "-" for be in a.backends]
        print("| " + " | ".join(cells) + " |")
    sys.exit(1 if failed else 0)

if __name__ == "__main__":
    main()
