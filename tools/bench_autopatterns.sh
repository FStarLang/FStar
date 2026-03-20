#!/bin/bash
set -uo pipefail

FSTAR_ROOT="/home/nswamy/clean/FStar"
FSTAR="$FSTAR_ROOT/stage3/out/bin/fstar.exe"
WORKDIR="/tmp/bench-v4"
rm -rf "$WORKDIR"
mkdir -p "$WORKDIR/base" "$WORKDIR/head"

TARGETS="tests/micro-benchmarks tests/bug-reports tests/calc tests/coercions tests/typeclasses tests/tactics tests/semiring tests/projectors tests/error-messages tests/friends tests/hacl tests/vale examples/algorithms examples/data_structures examples/demos examples/dm4free examples/dsls examples/indexed_effects examples/layeredeffects examples/metatheory examples/misc examples/oplss2021 examples/paradoxes examples/param examples/preorders examples/rel examples/software_foundations examples/tactics examples/termination examples/typeclasses examples/verifythis"

run_config() {
  local label=$1 outdir=$2 extra_flags=$3
  cd "$FSTAR_ROOT"

  echo "=== $label: Rebuilding ulib ==="
  rm -rf stage2/ulib.checked && mkdir -p stage2/ulib.checked
  env SRC=ulib/ FSTAR_EXE="$FSTAR" CACHE_DIR=stage2/ulib.checked/ OUTPUT_DIR=stage2/ulib.ml/ \
      CODEGEN=OCaml TAG=lib OTHERFLAGS="$extra_flags --warn_error -271" TOUCH=".alib_${label}.src.touch" \
      make -f mk/lib.mk verify -j16 -sk 2>&1 | tail -1
  rm -f stage3/out/lib/fstar/ulib.checked
  ln -sf "$FSTAR_ROOT/stage2/ulib.checked" stage3/out/lib/fstar/ulib.checked

  echo "=== $label: Rebuilding Pulse lib ==="
  rm -rf pulse/build/lib.pulse.checked pulse/build/lib.common.checked pulse/build/lib.core.checked 2>/dev/null || true
  mkdir -p pulse/build

  /usr/bin/time -v -o "$outdir/pulse_core.time" \
    make -C pulse/ -f mk/lib-common.mk FSTAR_EXE="$FSTAR" \
      OTHERFLAGS="$extra_flags --timing --query_stats --warn_error -271" \
      -j16 -sk \
    > "$outdir/pulse_core.stdout" 2> "$outdir/pulse_core.stderr" || true
  echo "  pulse core done"

  /usr/bin/time -v -o "$outdir/pulse_lib.time" \
    make -C pulse/ -f mk/lib-pulse.mk FSTAR_EXE="$FSTAR" \
      OTHERFLAGS="$extra_flags --timing --query_stats --warn_error -271" \
      -j16 -sk \
    > "$outdir/pulse_lib.stdout" 2> "$outdir/pulse_lib.stderr" || true
  echo "  pulse lib done"

  echo "=== $label: F* tests+examples ==="
  date -u "+%Y-%m-%dT%H:%M:%SZ" > "$outdir/start.txt"
  for dir in $TARGETS; do
    local tag
    tag=$(echo "$dir" | tr '/' '_')
    local fulldir="$FSTAR_ROOT/$dir"
    [ -d "$fulldir" ] || continue
    rm -rf "$fulldir/_cache" 2>/dev/null
    /usr/bin/time -v -o "$outdir/${tag}.time" \
      make -C "$fulldir" all FSTAR_EXE="$FSTAR" \
        OTHERFLAGS="$extra_flags --timing --query_stats --warn_error -271" \
        -j16 -sk \
      > "$outdir/${tag}.stdout" 2> "$outdir/${tag}.stderr" || true
    echo -n "."
  done
  echo ""

  # Pulse tests
  rm -rf pulse/test/_cache 2>/dev/null
  /usr/bin/time -v -o "$outdir/pulse_test.time" \
    make -C pulse/test/ FSTAR_EXE="$FSTAR" STAGE3=1 \
      OTHERFLAGS="$extra_flags --timing --query_stats --warn_error -271" \
      -j16 -sk \
    > "$outdir/pulse_test.stdout" 2> "$outdir/pulse_test.stderr" || true
  echo "  pulse test done"

  date -u "+%Y-%m-%dT%H:%M:%SZ" > "$outdir/end.txt"
  echo "=== $label: Done ==="
}

run_config "baseline" "$WORKDIR/base" "--ext auto_patterns=false"
run_config "head" "$WORKDIR/head" ""

echo "=== Report ==="
python3 - "$WORKDIR" << 'PYREPORT'
import sys, os, re
workdir = sys.argv[1]
def parse_time(f):
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
tags = set()
for d in ['base', 'head']:
    for f in os.listdir(os.path.join(workdir, d)):
        if f.endswith('.time'): tags.add(f[:-5])
rows = []
for tag in sorted(tags):
    bw = parse_time(os.path.join(workdir, 'base', tag + '.time'))
    hw = parse_time(os.path.join(workdir, 'head', tag + '.time'))
    bq, brl, bqt = count_stats(os.path.join(workdir, 'base', tag + '.stdout'))
    hq, hrl, hqt = count_stats(os.path.join(workdir, 'head', tag + '.stdout'))
    rows.append(dict(tag=tag, bw=bw, hw=hw, bq=bq, hq=hq, brl=brl, hrl=hrl, bqt=bqt, hqt=hqt))
tw_b = sum(r['bw'] for r in rows); tw_h = sum(r['hw'] for r in rows)
tq_b = sum(r['bq'] for r in rows); tq_h = sum(r['hq'] for r in rows)
trl_b = sum(r['brl'] for r in rows); trl_h = sum(r['hrl'] for r in rows)
tqt_b = sum(r['bqt'] for r in rows); tqt_h = sum(r['hqt'] for r in rows)
R = []
R.append("=" * 130)
R.append("  FULL BENCHMARK: F* tests+examples + Pulse core+lib+tests")
R.append("=" * 130)
R.append("")
hdr = "%-40s %8s %8s %8s %7s  %6s %6s %9s %9s %7s" % (
    "Target", "Base(s)", "Head(s)", "D(s)", "D(%)", "BQ", "HQ", "BRlim", "HRlim", "DRl(%)")
R.append(hdr)
R.append("-" * 130)
for r in rows:
    dw = r['hw'] - r['bw']
    dpct = (dw / r['bw'] * 100) if r['bw'] > 1 else 0
    drl = ((r['hrl'] - r['brl']) / r['brl'] * 100) if r['brl'] > 0.1 else 0
    R.append("%-40s %8.1f %8.1f %+8.1f %+6.1f%%  %6d %6d %9.1f %9.1f %+6.1f%%" % (
        r['tag'], r['bw'], r['hw'], dw, dpct, r['bq'], r['hq'], r['brl'], r['hrl'], drl))
R.append("-" * 130)
tdpct = (tw_h - tw_b) / tw_b * 100 if tw_b > 0 else 0
tdrl = (trl_h - trl_b) / trl_b * 100 if trl_b > 0 else 0
R.append("%-40s %8.1f %8.1f %+8.1f %+6.1f%%  %6d %6d %9.1f %9.1f %+6.1f%%" % (
    "TOTAL", tw_b, tw_h, tw_h-tw_b, tdpct, tq_b, tq_h, trl_b, trl_h, tdrl))
R.append("")
R.append("Targets: %d" % len(rows))
R.append("Wall time:  %.1fs -> %.1fs  (%+.1f%%)" % (tw_b, tw_h, tdpct))
R.append("Z3 time:    %.1fs -> %.1fs  (%+.1f%%)" % (tqt_b/1000, tqt_h/1000, (tqt_h-tqt_b)/tqt_b*100 if tqt_b else 0))
R.append("Rlimit:     %.1f -> %.1f  (%+.1f%%)" % (trl_b, trl_h, tdrl))
R.append("Queries:    %d -> %d  (%+d)" % (tq_b, tq_h, tq_h-tq_b))
txt = "\n".join(R)
print(txt)
with open(os.path.join(workdir, "report.txt"), "w") as f: f.write(txt + "\n")
PYREPORT
