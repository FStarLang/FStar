#!/usr/bin/env bash
#
# bench_autopatterns_full.sh — Full-repo benchmark for auto_patterns
#
# Runs ALL F* verification targets (ulib, tests, examples) twice:
#   1. Baseline:        fstar2 behavior (no auto_patterns)
#   2. Auto-patterns:   with --ext auto_patterns
#
# Uses the Makefile infrastructure for dependency resolution and
# parallelism.  Collects --timing and --query_stats output, plus
# GNU time for overall resource usage per make target.
#
# Usage:
#   ./tools/bench_autopatterns_full.sh [WORKDIR] [JOBS]
#
# WORKDIR defaults to /tmp/bench-full-<timestamp>
# JOBS    defaults to 8
#
set -euo pipefail

FSTAR_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
FSTAR_EXE="$FSTAR_ROOT/stage1/out/bin/fstar.exe"
WORKDIR="${1:-/tmp/bench-full-$(date +%s)}"
JOBS="${2:-8}"
TIME_CMD="/usr/bin/time"

info()  { printf '==> %s\n' "$*"; }
bold()  { printf '\033[1m%s\033[0m\n' "$*"; }

mkdir -p "$WORKDIR"

if [ ! -x "$FSTAR_EXE" ]; then
  echo "ERROR: $FSTAR_EXE not found. Run 'make stage1' first."
  exit 1
fi

# ──────────────────────────────────────────────────
# Targets to benchmark
# ──────────────────────────────────────────────────
# Each entry: directory,make_target
TARGETS=(
  "tests/micro-benchmarks,all"
  "tests/bug-reports,all"
  "tests/calc,all"
  "tests/coercions,all"
  "tests/error-messages,all"
  "tests/friends,all"
  "tests/typeclasses,all"
  "tests/semiring,all"
  "tests/projectors,all"
  "tests/tactics,all"
  "examples/algorithms,all"
  "examples/data_structures,all"
  "examples/demos,all"
  "examples/dm4free,all"
  "examples/dsls,all"
  "examples/indexed_effects,all"
  "examples/layeredeffects,all"
  "examples/metatheory,all"
  "examples/misc,all"
  "examples/oplss2021,all"
  "examples/paradoxes,all"
  "examples/param,all"
  "examples/preorders,all"
  "examples/software_foundations,all"
  "examples/tactics,all"
  "examples/termination,all"
  "examples/typeclasses,all"
  "examples/verifythis,all"
)

# ──────────────────────────────────────────────────
# Run one configuration
# ──────────────────────────────────────────────────
run_config() {
  local label=$1 outdir=$2 extra_flags=$3

  mkdir -p "$outdir"

  info "[$label] Starting full benchmark (${#TARGETS[@]} targets, -j$JOBS)..."
  echo "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$outdir/start_time.txt"

  local pass=0 fail=0 skip=0

  for entry in "${TARGETS[@]}"; do
    local dir="${entry%%,*}"
    local target="${entry##*,}"
    local tag=$(echo "$dir" | tr '/' '_')
    local fulldir="$FSTAR_ROOT/$dir"

    if [ ! -d "$fulldir" ]; then
      info "[$label]   SKIP $dir (not found)"
      skip=$((skip + 1))
      continue
    fi

    info "[$label]   $dir ($target)"

    # Clean cache for fresh run
    rm -rf "$fulldir/_cache" 2>/dev/null || true

    # Run make with timing + query_stats, capture stdout+stderr
    $TIME_CMD -v -o "$outdir/${tag}.time" \
      make -C "$fulldir" "$target" \
        FSTAR_EXE="$FSTAR_EXE" \
        OTHERFLAGS="$extra_flags --timing --query_stats --warn_error -271" \
        -j"$JOBS" -sk \
      > "$outdir/${tag}.stdout" \
      2> "$outdir/${tag}.make_stderr" || true

    # Check for verification errors (not make errors)
    local errs=$(grep -c '^\* Error [0-9]' "$outdir/${tag}.stdout" 2>/dev/null || echo 0)
    if [ "$errs" -gt 0 ]; then
      fail=$((fail + 1))
    else
      pass=$((pass + 1))
    fi
  done

  echo "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$outdir/end_time.txt"
  info "[$label] Done: $pass pass, $fail with errors, $skip skipped"
}

# ──────────────────────────────────────────────────
# Extract metrics from a run
# ──────────────────────────────────────────────────
extract_all_metrics() {
  local label=$1 indir=$2 outfile=$3

  info "[$label] Extracting metrics..."

  python3 - "$indir" "$outfile" << 'PYEXTRACT'
import sys, os, re

indir = sys.argv[1]
outfile = sys.argv[2]

results = []
for tf in sorted(os.listdir(indir)):
    if not tf.endswith('.time'):
        continue
    tag = tf[:-5]

    # Parse GNU time output
    wall = user = syst = rss = 0
    try:
        with open(os.path.join(indir, tf)) as f:
            for line in f:
                m = re.search(r'wall clock.*?(\d+):(\d+\.\d+)', line)
                if m: wall = float(m.group(1))*60 + float(m.group(2))
                m = re.search(r'User time.*?(\d+\.\d+)', line)
                if m: user = float(m.group(1))
                m = re.search(r'System time.*?(\d+\.\d+)', line)
                if m: syst = float(m.group(1))
                m = re.search(r'Maximum resident.*?(\d+)', line)
                if m: rss = int(m.group(1))
    except: pass

    # Parse query stats from stdout
    stdout_file = os.path.join(indir, tag + '.stdout')
    n_queries = n_succ = n_fail = 0
    total_qtime = 0
    total_rlimit = 0.0
    try:
        with open(stdout_file) as f:
            for line in f:
                m = re.search(r'Query-stats.*succeeded in (\d+) milliseconds.*used rlimit ([\d.]+)', line)
                if m:
                    n_queries += 1
                    n_succ += 1
                    total_qtime += int(m.group(1))
                    total_rlimit += float(m.group(2))
                elif 'Query-stats' in line and 'failed' in line:
                    n_queries += 1
                    n_fail += 1
                    m2 = re.search(r'in (\d+) milliseconds', line)
                    if m2: total_qtime += int(m2.group(1))
    except: pass

    results.append({
        'tag': tag, 'wall': wall, 'user': user, 'sys': syst,
        'rss': rss, 'queries': n_queries, 'succ': n_succ,
        'fail': n_fail, 'qtime_ms': total_qtime, 'rlimit': total_rlimit
    })

with open(outfile, 'w') as out:
    out.write(f"{'Target':<40} {'Wall(s)':>8} {'User(s)':>8} {'Sys(s)':>7} {'RSS(MB)':>8} {'Queries':>8} {'Succ':>6} {'Fail':>6} {'QTime(s)':>9} {'Rlimit':>9}\n")
    out.write("─" * 120 + "\n")

    tw = tu = ts = tq = 0; tqs = tqf = 0; trl = 0.0
    for r in results:
        tw += r['wall']; tu += r['user']; ts += r['sys']
        tq += r['queries']; tqs += r['succ']; tqf += r['fail']
        trl += r['rlimit']
        out.write(f"{r['tag']:<40} {r['wall']:8.1f} {r['user']:8.1f} {r['sys']:7.1f} {r['rss']/1024:8.0f} {r['queries']:8} {r['succ']:6} {r['fail']:6} {r['qtime_ms']/1000:9.1f} {r['rlimit']:9.1f}\n")

    out.write("─" * 120 + "\n")
    out.write(f"{'TOTAL':<40} {tw:8.1f} {tu:8.1f} {ts:7.1f} {'':>8} {tq:8} {tqs:6} {tqf:6} {0:9.1f} {trl:9.1f}\n")

print(f"Wrote {outfile}")
PYEXTRACT
}

# ──────────────────────────────────────────────────
# Generate comparison report
# ──────────────────────────────────────────────────
generate_report() {
  local report="$WORKDIR/report.txt"

  info "Generating comparison report..."

  python3 - "$WORKDIR" "$report" << 'PYREPORT'
import sys, os, re

workdir = sys.argv[1]
report_path = sys.argv[2]

def parse_metrics(f):
    rows = []
    try:
        with open(f) as fh:
            lines = fh.readlines()
            for line in lines[2:]:  # skip header + separator
                if line.startswith("─") or line.startswith("TOTAL"):
                    continue
                parts = line.split()
                if len(parts) >= 10:
                    rows.append({
                        'tag': parts[0],
                        'wall': float(parts[1]),
                        'user': float(parts[2]),
                        'sys': float(parts[3]),
                        'rss': float(parts[4]),
                        'queries': int(parts[5]),
                        'succ': int(parts[6]),
                        'fail': int(parts[7]),
                        'qtime': float(parts[8]),
                        'rlimit': float(parts[9]),
                    })
    except Exception as e:
        print(f"Warning parsing {f}: {e}")
    return rows

base = parse_metrics(os.path.join(workdir, 'base_metrics.txt'))
head = parse_metrics(os.path.join(workdir, 'head_metrics.txt'))

base_map = {r['tag']: r for r in base}
head_map = {r['tag']: r for r in head}

all_tags = sorted(set(list(base_map.keys()) + list(head_map.keys())))

with open(report_path, 'w') as rpt:
    rpt.write("=" * 130 + "\n")
    rpt.write("  COMPREHENSIVE AUTO-PATTERNS BENCHMARKING REPORT\n")
    rpt.write("=" * 130 + "\n\n")

    start_b = open(os.path.join(workdir, 'base/start_time.txt')).read().strip() if os.path.exists(os.path.join(workdir, 'base/start_time.txt')) else '?'
    end_b = open(os.path.join(workdir, 'base/end_time.txt')).read().strip() if os.path.exists(os.path.join(workdir, 'base/end_time.txt')) else '?'
    start_h = open(os.path.join(workdir, 'head/start_time.txt')).read().strip() if os.path.exists(os.path.join(workdir, 'head/start_time.txt')) else '?'
    end_h = open(os.path.join(workdir, 'head/end_time.txt')).read().strip() if os.path.exists(os.path.join(workdir, 'head/end_time.txt')) else '?'

    rpt.write(f"Baseline run:      {start_b} to {end_b}\n")
    rpt.write(f"Auto-patterns run: {start_h} to {end_h}\n\n")

    # ── Side-by-side comparison ──
    rpt.write("=" * 130 + "\n")
    rpt.write("  SIDE-BY-SIDE: Wall-clock time per target\n")
    rpt.write("=" * 130 + "\n\n")

    header = f"{'Target':<40} {'Base(s)':>8} {'Head(s)':>8} {'Δ(s)':>8} {'Δ(%)':>7}  {'BaseQ':>6} {'HeadQ':>6} {'BaseRlim':>9} {'HeadRlim':>9} {'ΔRlim':>9}"
    rpt.write(header + "\n")
    rpt.write("─" * 130 + "\n")

    tw_b = tw_h = 0.0
    tq_b = tq_h = 0
    trl_b = trl_h = 0.0
    regression_tags = []
    speedup_tags = []

    for tag in all_tags:
        b = base_map.get(tag)
        h = head_map.get(tag)
        if not b or not h:
            rpt.write(f"{tag:<40} {'(missing)':>8} {'(missing)':>8}\n")
            continue

        dw = h['wall'] - b['wall']
        dpct = (dw / b['wall'] * 100) if b['wall'] > 0 else 0
        drl = h['rlimit'] - b['rlimit']

        tw_b += b['wall']; tw_h += h['wall']
        tq_b += b['queries']; tq_h += h['queries']
        trl_b += b['rlimit']; trl_h += h['rlimit']

        flag = ""
        if dpct > 10 and dw > 1: flag = " ⚠️"; regression_tags.append((tag, dpct, dw))
        elif dpct < -10 and dw < -1: flag = " 🚀"; speedup_tags.append((tag, dpct, dw))

        rpt.write(f"{tag:<40} {b['wall']:8.1f} {h['wall']:8.1f} {dw:+8.1f} {dpct:+6.1f}%  {b['queries']:6} {h['queries']:6} {b['rlimit']:9.1f} {h['rlimit']:9.1f} {drl:+9.1f}{flag}\n")

    rpt.write("─" * 130 + "\n")
    total_dpct = ((tw_h - tw_b) / tw_b * 100) if tw_b > 0 else 0
    total_drl = trl_h - trl_b
    rpt.write(f"{'TOTAL':<40} {tw_b:8.1f} {tw_h:8.1f} {tw_h-tw_b:+8.1f} {total_dpct:+6.1f}%  {tq_b:6} {tq_h:6} {trl_b:9.1f} {trl_h:9.1f} {total_drl:+9.1f}\n\n")

    # ── Query comparison ──
    rpt.write("=" * 130 + "\n")
    rpt.write("  QUERY STATISTICS\n")
    rpt.write("=" * 130 + "\n\n")
    rpt.write(f"Total queries (baseline):       {tq_b}\n")
    rpt.write(f"Total queries (auto_patterns):  {tq_h}\n")
    rpt.write(f"Total rlimit  (baseline):       {trl_b:.1f}\n")
    rpt.write(f"Total rlimit  (auto_patterns):  {trl_h:.1f}\n")
    rpt.write(f"Rlimit delta:                   {total_drl:+.1f} ({total_drl/trl_b*100 if trl_b else 0:+.2f}%)\n\n")

    # ── Summary ──
    rpt.write("=" * 130 + "\n")
    rpt.write("  SUMMARY\n")
    rpt.write("=" * 130 + "\n\n")
    rpt.write(f"Targets benchmarked:  {len(all_tags)}\n")
    rpt.write(f"Total wall time (baseline):       {tw_b:.1f}s ({tw_b/60:.1f}m)\n")
    rpt.write(f"Total wall time (auto_patterns):  {tw_h:.1f}s ({tw_h/60:.1f}m)\n")
    rpt.write(f"Overall time delta:               {tw_h-tw_b:+.1f}s ({total_dpct:+.1f}%)\n\n")

    if regression_tags:
        rpt.write(f"Regressions (>10% slower, >1s):\n")
        for tag, pct, dw in sorted(regression_tags, key=lambda x: -x[1]):
            rpt.write(f"  ⚠️  {tag}: {pct:+.1f}% ({dw:+.1f}s)\n")
        rpt.write("\n")
    else:
        rpt.write("Regressions (>10% slower, >1s): NONE\n\n")

    if speedup_tags:
        rpt.write(f"Speedups (>10% faster, >1s):\n")
        for tag, pct, dw in sorted(speedup_tags, key=lambda x: x[1]):
            rpt.write(f"  🚀 {tag}: {pct:+.1f}% ({dw:+.1f}s)\n")
        rpt.write("\n")

print(f"Report: {report_path}")
PYREPORT

  cat "$report"
}

# ──────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────
bold "Full-repo auto_patterns benchmark"
info "F* binary: $FSTAR_EXE"
info "Work dir:  $WORKDIR"
info "Targets:   ${#TARGETS[@]}"
info "Jobs:      $JOBS"
echo ""

# Run baseline
run_config "base" "$WORKDIR/base" ""

# Run with auto_patterns
run_config "head" "$WORKDIR/head" "--ext auto_patterns"

# Extract metrics
extract_all_metrics "base" "$WORKDIR/base" "$WORKDIR/base_metrics.txt"
extract_all_metrics "head" "$WORKDIR/head" "$WORKDIR/head_metrics.txt"

# Report
generate_report

bold "Done! Full results in $WORKDIR"
