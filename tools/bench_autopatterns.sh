#!/bin/bash
#
# bench_autopatterns.sh — Benchmark auto_patterns vs baseline
#
# Clones the repo twice, does a full clean build + test in each,
# and compares query_stats output.
#
# Usage:
#   ./tools/bench_autopatterns.sh [WORKDIR]
#
# WORKDIR defaults to /tmp/bench-autopatterns-<timestamp>
#
set -uo pipefail

REPO_DIR="$(cd "$(dirname "$0")/.." && pwd)"
WORKDIR="${1:-/tmp/bench-autopatterns-$(date +%s)}"
BASE_DIR="$WORKDIR/base"
HEAD_DIR="$WORKDIR/head"

echo "=== Auto-patterns benchmark ==="
echo "Repo:    $REPO_DIR"
echo "Workdir: $WORKDIR"
echo ""

mkdir -p "$WORKDIR"

# Clone twice
echo "=== Cloning baseline ==="
git clone "$REPO_DIR" "$BASE_DIR"
echo "=== Cloning head ==="
git clone "$REPO_DIR" "$HEAD_DIR"

# Baseline: build + test with auto_patterns=false
echo "=== BASELINE: make test (auto_patterns=false) ==="
cd "$BASE_DIR"
/usr/bin/time -v -o "$WORKDIR/base.time" \
  make test \
    OTHERFLAGS="--ext auto_patterns=false --timing --query_stats --warn_error -271" \
    -j$(nproc) -sk \
  > "$WORKDIR/base.stdout" 2> "$WORKDIR/base.stderr" || true
echo "=== BASELINE DONE ==="

# Head: build + test with auto_patterns=true (default)
echo "=== HEAD: make test (auto_patterns=true, default) ==="
cd "$HEAD_DIR"
/usr/bin/time -v -o "$WORKDIR/head.time" \
  make test \
    OTHERFLAGS="--timing --query_stats --warn_error -271" \
    -j$(nproc) -sk \
  > "$WORKDIR/head.stdout" 2> "$WORKDIR/head.stderr" || true
echo "=== HEAD DONE ==="

# Report
echo "=== Generating report ==="
python3 - "$WORKDIR" << 'PYREPORT'
import sys, os, re

workdir = sys.argv[1]

def parse_wall(f):
    try:
        with open(f) as fh:
            for line in fh:
                m = re.search(r'wall clock.*?(\d+):(\d+\.\d+)', line)
                if m: return float(m.group(1))*60 + float(m.group(2))
    except: pass
    return 0

def count_stats(f):
    nq = 0; rl = 0.0; qtime = 0
    try:
        with open(f) as fh:
            for line in fh:
                m = re.search(r'Query-stats.*succeeded in (\d+) milliseconds.*used rlimit ([\d.]+)', line)
                if m: nq += 1; rl += float(m.group(2)); qtime += int(m.group(1))
                elif 'Query-stats' in line and 'failed' in line: nq += 1
    except: pass
    return nq, rl, qtime

bw = parse_wall(os.path.join(workdir, 'base.time'))
hw = parse_wall(os.path.join(workdir, 'head.time'))
bq, brl, bqt = count_stats(os.path.join(workdir, 'base.stdout'))
hq, hrl, hqt = count_stats(os.path.join(workdir, 'head.stdout'))

R = []
R.append("=" * 70)
R.append("  auto_patterns benchmark: make test")
R.append("  baseline = --ext auto_patterns=false")
R.append("  head     = auto_patterns=true (default)")
R.append("=" * 70)
R.append("")
R.append("%-20s %12s %12s %15s" % ("Metric", "Baseline", "Head", "Delta"))
R.append("-" * 65)
R.append("%-20s %12.1f %12.1f %+10.1f (%+.1f%%)" % (
    "Wall time (s)", bw, hw, hw-bw, (hw-bw)/bw*100 if bw else 0))
R.append("%-20s %12.1f %12.1f %+10.1f (%+.1f%%)" % (
    "Z3 time (s)", bqt/1000, hqt/1000, (hqt-bqt)/1000,
    (hqt-bqt)/bqt*100 if bqt else 0))
R.append("%-20s %12.1f %12.1f %+10.1f (%+.1f%%)" % (
    "Z3 rlimit", brl, hrl, hrl-brl,
    (hrl-brl)/brl*100 if brl else 0))
R.append("%-20s %12d %12d %+10d" % ("Queries", bq, hq, hq-bq))

txt = "\n".join(R)
print(txt)
rpt = os.path.join(workdir, "report.txt")
with open(rpt, "w") as f:
    f.write(txt + "\n")
print("\nReport: " + rpt)
PYREPORT
