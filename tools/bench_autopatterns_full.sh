#!/bin/bash
set -euo pipefail

FSTAR_ROOT="/home/nswamy/clean/FStar"
FSTAR_EXE="$FSTAR_ROOT/stage1/out/bin/fstar.exe"
WORKDIR="/tmp/bench-proper2"
mkdir -p "$WORKDIR"

TARGETS=(
  tests/micro-benchmarks tests/bug-reports tests/calc tests/coercions
  tests/typeclasses tests/tactics tests/semiring tests/projectors
  tests/error-messages tests/friends
  examples/algorithms examples/data_structures examples/demos
  examples/dm4free examples/dsls examples/indexed_effects
  examples/layeredeffects examples/metatheory examples/misc
  examples/oplss2021 examples/paradoxes examples/param
  examples/preorders examples/software_foundations examples/tactics
  examples/termination examples/typeclasses examples/verifythis
)

run_config() {
  local label=$1 outdir=$2 extra_flags=$3
  mkdir -p "$outdir"
  
  echo "=== $label: Rebuilding ulib ==="
  cd "$FSTAR_ROOT"
  rm -rf stage1/ulib.checked
  mkdir -p stage1/ulib.checked
  env SRC=ulib/ FSTAR_EXE="$FSTAR_EXE" \
      CACHE_DIR=stage1/ulib.checked/ OUTPUT_DIR=stage1/ulib.ml/ \
      CODEGEN=OCaml TAG=lib \
      TOUCH=".alib_${label}.src.touch" \
      OTHERFLAGS="$extra_flags --warn_error -271" \
      make -f mk/lib.mk verify -j8 -sk 2>&1 | tail -3
  rm -f stage1/out/lib/fstar/ulib.checked
  ln -s ../../../ulib.checked stage1/out/lib/fstar/ulib.checked

  echo "=== $label: Running ${#TARGETS[@]} targets ==="
  date -u "+%Y-%m-%dT%H:%M:%SZ" > "$outdir/start.txt"
  
  # Clean all caches
  for dir in "${TARGETS[@]}"; do
    rm -rf "$FSTAR_ROOT/$dir/_cache" 2>/dev/null || true
  done
  
  for dir in "${TARGETS[@]}"; do
    local tag
    tag=$(echo "$dir" | tr '/' '_')
    local fulldir="$FSTAR_ROOT/$dir"
    [ -d "$fulldir" ] || continue
    
    echo "[$label] $dir"
    /usr/bin/time -v -o "$outdir/${tag}.time" \
      env OTHERFLAGS="$extra_flags --timing --query_stats --warn_error -271" \
      make -C "$fulldir" all \
        FSTAR_EXE="$FSTAR_EXE" \
        -j8 -sk \
      > "$outdir/${tag}.stdout" 2> "$outdir/${tag}.stderr" || true
  done
  
  date -u "+%Y-%m-%dT%H:%M:%SZ" > "$outdir/end.txt"
  echo "=== $label: Done ==="
}

# Run baseline
run_config "baseline" "$WORKDIR/base" ""

# Run auto_patterns  
run_config "autopatterns" "$WORKDIR/head" "--ext auto_patterns"

# Generate report
echo "=== Generating report ==="
python3 "$FSTAR_ROOT/tools/bench_autopatterns_full.sh" --report-only "$WORKDIR" 2>/dev/null || \
python3 - "$WORKDIR" << 'PYREPORT'
import sys, os, re

workdir = sys.argv[1]
report_path = os.path.join(workdir, "report.txt")

def parse_time(f):
    d = {}
    try:
        with open(f) as fh:
            for line in fh:
                m = re.search(r'wall clock.*?(\d+):(\d+\.\d+)', line)
                if m: d['wall'] = float(m.group(1))*60 + float(m.group(2))
                m = re.search(r'User time.*?(\d+\.\d+)', line)
                if m: d['user'] = float(m.group(1))
                m = re.search(r'Maximum resident.*?(\d+)', line)
                if m: d['rss'] = int(m.group(1))
    except: pass
    return d

def count_stats(f):
    nq = ns = nf = 0; rl = 0.0
    try:
        with open(f) as fh:
            for line in fh:
                m = re.search(r'Query-stats.*succeeded in (\d+) milliseconds.*used rlimit ([\d.]+)', line)
                if m: nq += 1; ns += 1; rl += float(m.group(2))
                elif 'Query-stats' in line and 'failed' in line: nq += 1; nf += 1
    except: pass
    return nq, ns, nf, rl

tags = set()
for d in ['base', 'head']:
    dpath = os.path.join(workdir, d)
    if os.path.isdir(dpath):
        for f in os.listdir(dpath):
            if f.endswith('.time'): tags.add(f[:-5])

with open(report_path, 'w') as rpt:
    rpt.write("=" * 140 + "\n")
    rpt.write("  FULL F* REPO BENCHMARK: fstar2 (baseline) vs fstar2_autopatterns\n")
    rpt.write("=" * 140 + "\n\n")

    hdr = "%s %s %s %s %s  %s %s %s %s\n" % (
        "Target".ljust(40), "Base(s)".rjust(8), "Head(s)".rjust(8), "D(s)".rjust(8), "D(%)".rjust(7),
        "BQ".rjust(5), "HQ".rjust(5), "BRlim".rjust(8), "HRlim".rjust(8))
    rpt.write(hdr)
    rpt.write("-" * 140 + "\n")

    tw_b = tw_h = trl_b = trl_h = 0.0; tq_b = tq_h = 0

    for tag in sorted(tags):
        b = parse_time(os.path.join(workdir, 'base', tag + '.time'))
        h = parse_time(os.path.join(workdir, 'head', tag + '.time'))
        bq, bs, bf, brl = count_stats(os.path.join(workdir, 'base', tag + '.stdout'))
        hq, hs, hf, hrl = count_stats(os.path.join(workdir, 'head', tag + '.stdout'))
        bw = b.get('wall', 0); hw = h.get('wall', 0)
        tw_b += bw; tw_h += hw; tq_b += bq; tq_h += hq; trl_b += brl; trl_h += hrl
        dw = hw - bw
        dpct = "%.1f" % (dw / bw * 100) if bw > 1 else "n/a"
        rpt.write("%s %8.1f %8.1f %+8.1f %7s  %5d %5d %8.1f %8.1f\n" % (
            tag.ljust(40), bw, hw, dw, dpct, bq, hq, brl, hrl))

    rpt.write("-" * 140 + "\n")
    total_dpct = "%.1f" % ((tw_h - tw_b) / tw_b * 100) if tw_b > 0 else "n/a"
    total_drl = "%.1f" % ((trl_h - trl_b) / trl_b * 100) if trl_b > 0 else "n/a"
    rpt.write("%s %8.1f %8.1f %+8.1f %7s  %5d %5d %8.1f %8.1f\n\n" % (
        "TOTAL".ljust(40), tw_b, tw_h, tw_h-tw_b, total_dpct, tq_b, tq_h, trl_b, trl_h))

    rpt.write("Total rlimit delta: %s%%\n" % total_drl)
    rpt.write("Total query delta: %d -> %d\n" % (tq_b, tq_h))

print(open(report_path).read())
PYREPORT

echo "Report: $WORKDIR/report.txt"
