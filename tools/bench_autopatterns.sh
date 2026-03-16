#!/usr/bin/env bash
#
# bench_autopatterns.sh — Performance benchmark for auto_patterns
#
# Compares the fstar2 (baseline) branch against fstar2_autopatterns (head)
# using F*'s --query_stats, --timing, --log_queries, Z3's smt.qi.profile,
# and system-level resource monitoring (GNU time).
#
# Usage:
#   ./tools/bench_autopatterns.sh [WORKDIR]
#
# WORKDIR defaults to /tmp/bench-autopatterns-<timestamp>
#
# The script:
#   1. Clones both branches into separate directories
#   2. Builds stage1 for each
#   3. Runs a curated set of files with profiling flags
#   4. Collects timing, memory, query stats, QI profiles, and .smt2 files
#   5. Produces a detailed comparison report
#
# Requirements: git, GNU make, OCaml toolchain, /usr/bin/time, z3
#
set -euo pipefail

REPO_DIR="$(cd "$(dirname "$0")/.." && pwd)"
BASE_BRANCH="fstar2"
HEAD_BRANCH="fstar2_autopatterns"

WORKDIR="${1:-/tmp/bench-autopatterns-$(date +%s)}"
BASE_DIR="$WORKDIR/base"
HEAD_DIR="$WORKDIR/head"
RESULTS="$WORKDIR/results"

NPROC=$(nproc 2>/dev/null || echo 4)
# Use fewer cores for benchmarking to reduce noise
BENCH_JOBS=4
TIME_CMD="/usr/bin/time"

bold()  { printf '\033[1m%s\033[0m\n' "$*"; }
info()  { printf '==> %s\n' "$*"; }
error() { printf 'ERROR: %s\n' "$*" >&2; }

# ──────────────────────────────────────────────────────────────
# Benchmark suite: curated set of files that exercise quantifiers
# ──────────────────────────────────────────────────────────────
# These files were chosen to cover:
#   - Files with many quantifiers (good for measuring pattern inference impact)
#   - Files from ulib, tests, examples (breadth)
#   - Files that had regressions (to verify {:nopattern} fixes performance)
BENCH_FILES=(
  # ulib core
  "ulib/FStar.List.Tot.Properties.fst"
  "ulib/FStar.Seq.Properties.fst"
  "ulib/FStar.Seq.Base.fst"
  "ulib/FStar.Set.fst"
  "ulib/FStar.Map.fst"
  "ulib/FStar.Classical.fst"
  "ulib/FStar.FunctionalExtensionality.fsti"
  "ulib/FStar.Pervasives.fsti"
  "ulib/FStar.Math.Lemmas.fst"
  "ulib/FStar.UInt.fst"
  # tests
  "tests/micro-benchmarks/Arith.fst"
  "tests/micro-benchmarks/AutoPatterns.fst"
  "tests/micro-benchmarks/ClassicalSugar.fst"
  # examples with quantifiers (now with {:nopattern} fixes)
  "examples/algorithms/QuickSort.List.fst"
  "examples/data_structures/BinarySearchTree.fst"
  "examples/data_structures/BinarySearchTreeBasic.fst"
  "examples/termination/Termination.fst"
)

# ──────────────────────────────────────────────────────────────
# Phase 1: Clone / setup
# ──────────────────────────────────────────────────────────────
phase_clone() {
  local label=$1 branch=$2 dir=$3
  if [ -d "$dir/.git" ]; then
    info "[$label] Already cloned at $dir"
    git -C "$dir" fetch origin "$branch" 2>/dev/null || true
    git -C "$dir" checkout "$branch" 2>/dev/null
    git -C "$dir" reset --hard "origin/$branch" 2>/dev/null || git -C "$dir" reset --hard "$branch"
  else
    info "[$label] Cloning from $REPO_DIR branch=$branch into $dir"
    git clone --branch "$branch" --single-branch "$REPO_DIR" "$dir"
  fi
  git -C "$dir" rev-parse HEAD > "$dir/commit.txt"
  info "[$label] HEAD = $(cat "$dir/commit.txt" | head -c 12)"
}

# ──────────────────────────────────────────────────────────────
# Phase 2: Build
# ──────────────────────────────────────────────────────────────
phase_build() {
  local label=$1 dir=$2
  local fstar="$dir/stage1/out/bin/fstar.exe"
  if [ -x "$fstar" ]; then
    info "[$label] fstar.exe already exists, skipping build"
    return 0
  fi
  info "[$label] Building stage1 (this takes ~15 min)..."
  make -C "$dir" stage1 -j"$NPROC" 2>&1 | tail -5
  if [ ! -x "$fstar" ]; then
    error "[$label] Build failed"
    return 1
  fi
  info "[$label] Build OK"
}

# ──────────────────────────────────────────────────────────────
# Phase 3: Run benchmarks with profiling
# ──────────────────────────────────────────────────────────────
run_single_file() {
  local fstar=$1 file=$2 outdir=$3 extra_flags=$4
  local basename
  basename=$(echo "$file" | tr '/' '__' | sed 's/\.fst[i]*$//')

  mkdir -p "$outdir"

  # Build the fstar command
  local cmd="$fstar $extra_flags --timing --query_stats --log_queries --z3smtopt '(set-option :smt.qi.profile true)' --z3smtopt '(set-option :smt.qi.profile_freq 10000)' --warn_error -271 $file"

  # Run with GNU time for wall-clock, user, system time, and peak RSS
  $TIME_CMD -v -o "$outdir/${basename}.time" \
    bash -c "$cmd" \
    > "$outdir/${basename}.stdout" \
    2> "$outdir/${basename}.stderr" || true

  # Collect .smt2 files produced by --log_queries
  local queries_dir
  queries_dir=$(dirname "$file")
  find "$queries_dir" -maxdepth 1 -name 'queries-*.smt2' -newer "$outdir/${basename}.time" 2>/dev/null | while read -r smt2; do
    mv "$smt2" "$outdir/" 2>/dev/null || true
  done

  # Extract query_stats summary
  grep -E '^\(|Query-stats|succeeded|failed' "$outdir/${basename}.stdout" > "$outdir/${basename}.query_stats" 2>/dev/null || true
}

phase_bench() {
  local label=$1 dir=$2 outdir=$3 extra_flags=$4
  local fstar="$dir/stage1/out/bin/fstar.exe"

  if [ -f "$outdir/.done" ]; then
    info "[$label] Benchmarks already done, skipping"
    return 0
  fi

  mkdir -p "$outdir"
  info "[$label] Running ${#BENCH_FILES[@]} benchmark files..."

  for file in "${BENCH_FILES[@]}"; do
    local fullpath="$dir/$file"
    if [ ! -f "$fullpath" ]; then
      info "[$label]   SKIP $file (not found)"
      continue
    fi
    info "[$label]   $file"
    run_single_file "$fstar" "$fullpath" "$outdir" "$extra_flags"
  done

  touch "$outdir/.done"
  info "[$label] Benchmark phase complete"
}

# ──────────────────────────────────────────────────────────────
# Phase 4: Extract metrics from results
# ──────────────────────────────────────────────────────────────
extract_metrics() {
  local label=$1 outdir=$2 summary=$3

  info "[$label] Extracting metrics..."

  # Header
  printf "%-55s %10s %10s %10s %12s %8s %8s %8s\n" \
    "File" "Wall(s)" "User(s)" "Sys(s)" "MaxRSS(KB)" "Queries" "QSucc" "QFail" \
    > "$summary"
  printf "%s\n" "$(printf '%.0s─' {1..130})" >> "$summary"

  for timefile in "$outdir"/*.time; do
    [ -f "$timefile" ] || continue
    local basename
    basename=$(basename "$timefile" .time)

    # Extract GNU time metrics
    local wall user sys maxrss
    wall=$(grep 'wall clock' "$timefile" | grep -oP '[\d:.]+' | tail -1 || echo "?")
    user=$(grep 'User time' "$timefile" | grep -oP '[\d.]+' || echo "?")
    sys=$(grep 'System time' "$timefile" | grep -oP '[\d.]+' || echo "?")
    maxrss=$(grep 'Maximum resident' "$timefile" | grep -oP '[\d]+' || echo "?")

    # Convert wall clock mm:ss.ss to seconds
    if echo "$wall" | grep -q ':'; then
      local mins secs
      mins=$(echo "$wall" | cut -d: -f1)
      secs=$(echo "$wall" | cut -d: -f2)
      wall=$(echo "$mins * 60 + $secs" | bc 2>/dev/null || echo "$wall")
    fi

    # Extract query stats
    local queries qsucc qfail
    local statsfile="$outdir/${basename}.stdout"
    queries=$(grep -c 'Query-stats' "$statsfile" 2>/dev/null || echo "0")
    qsucc=$(grep -c 'succeeded' "$statsfile" 2>/dev/null || echo "0")
    qfail=$(grep -c 'failed' "$statsfile" 2>/dev/null || echo "0")

    printf "%-55s %10s %10s %10s %12s %8s %8s %8s\n" \
      "$basename" "$wall" "$user" "$sys" "$maxrss" "$queries" "$qsucc" "$qfail" \
      >> "$summary"
  done

  # Totals
  printf "%s\n" "$(printf '%.0s─' {1..130})" >> "$summary"
  awk 'NR>2 && !/^─/ {w+=$2; u+=$3; s+=$4; m+=$5; q+=$6; qs+=$7; qf+=$8; n++}
       END {printf "%-55s %10.1f %10.1f %10.1f %12s %8d %8d %8d\n",
            "TOTAL ("n" files)", w, u, s, "-", q, qs, qf}' \
    "$summary" >> "$summary"

  echo "" >> "$summary"
  info "[$label] Metrics written to $summary"
}

# ──────────────────────────────────────────────────────────────
# Phase 5: Compare QI profiles from .smt2 output
# ──────────────────────────────────────────────────────────────
extract_qi_profile() {
  local label=$1 outdir=$2 qi_summary=$3

  info "[$label] Extracting Z3 QI profiles..."

  # Parse Z3's quantifier instantiation profile from stderr
  # Z3 outputs lines like: [quantifier_instances] name : count
  local stderrdir="$outdir"
  local total_qi=0
  local file_count=0

  printf "%-60s %12s\n" "Quantifier" "Instantiations" > "$qi_summary"
  printf "%s\n" "$(printf '%.0s─' {1..75})" >> "$qi_summary"

  for stderrfile in "$stderrdir"/*.stderr; do
    [ -f "$stderrfile" ] || continue
    # Z3's qi.profile outputs to stderr as:  [quantifier_instances]  quant_name :  N
    grep -oP '\[quantifier_instances\]\s+\S+\s*:\s*\d+' "$stderrfile" 2>/dev/null | \
      sed 's/\[quantifier_instances\]\s*//' | \
      while IFS=':' read -r name count; do
        count=$(echo "$count" | tr -d ' ')
        name=$(echo "$name" | tr -d ' ')
        echo "$name $count"
      done
    file_count=$((file_count + 1))
  done | sort | awk '{
    qi[$1] += $2
  } END {
    total = 0
    for (q in qi) {
      total += qi[q]
    }
    # Sort by count descending
    n = asorti(qi, sorted)
    PROCINFO["sorted_in"] = "@val_num_desc"
    for (q in qi) {
      if (qi[q] > 100) {
        printf "%-60s %12d\n", substr(q, 1, 60), qi[q]
      }
    }
    printf "%-60s %12d\n", "TOTAL", total
  }' >> "$qi_summary"

  echo "" >> "$qi_summary"
  info "[$label] QI profile written to $qi_summary"
}

# ──────────────────────────────────────────────────────────────
# Phase 6: Diff .smt2 files between branches
# ──────────────────────────────────────────────────────────────
strip_smt2_metadata() {
  sed -E \
    -e '/^;/d' \
    -e 's/uu___[0-9]+/uu___NNN/g' \
    -e 's/Non_total_Tm_arrow_[a-f0-9]+/Non_total_Tm_arrow_HASH/g' \
    -e 's/Tm_refine_[a-f0-9]+/Tm_refine_HASH/g' \
    -e 's/Tm_arrow_[a-f0-9]+/Tm_arrow_HASH/g' \
    "$1"
}

phase_diff_smt2() {
  local base_dir=$1 head_dir=$2 out=$3

  info "Comparing .smt2 files..."
  mkdir -p "$out/smt2_diffs"

  local base_smt2=() head_smt2=()
  for f in "$base_dir"/queries-*.smt2; do [ -f "$f" ] && base_smt2+=("$(basename "$f")"); done
  for f in "$head_dir"/queries-*.smt2; do [ -f "$f" ] && head_smt2+=("$(basename "$f")"); done

  local identical=0 semantic_diff=0 cosmetic_diff=0 only_base=0 only_head=0

  # Find common files
  comm -12 <(printf '%s\n' "${base_smt2[@]}" | sort) \
           <(printf '%s\n' "${head_smt2[@]}" | sort) 2>/dev/null | \
  while IFS= read -r f; do
    if diff -q "$base_dir/$f" "$head_dir/$f" >/dev/null 2>&1; then
      identical=$((identical + 1))
    elif diff <(strip_smt2_metadata "$base_dir/$f") \
              <(strip_smt2_metadata "$head_dir/$f") >/dev/null 2>&1; then
      cosmetic_diff=$((cosmetic_diff + 1))
    else
      semantic_diff=$((semantic_diff + 1))
      diff -u <(strip_smt2_metadata "$base_dir/$f") \
              <(strip_smt2_metadata "$head_dir/$f") \
        > "$out/smt2_diffs/$f.diff" 2>&1 || true
    fi
  done

  only_base=$(comm -23 <(printf '%s\n' "${base_smt2[@]}" | sort) \
                       <(printf '%s\n' "${head_smt2[@]}" | sort) 2>/dev/null | wc -l)
  only_head=$(comm -13 <(printf '%s\n' "${base_smt2[@]}" | sort) \
                       <(printf '%s\n' "${head_smt2[@]}" | sort) 2>/dev/null | wc -l)

  cat > "$out/smt2_summary.txt" <<EOF
=== SMT2 File Comparison ===
Base: $(cat "$WORKDIR/base/commit.txt" | head -c 12) ($BASE_BRANCH)
Head: $(cat "$WORKDIR/head/commit.txt" | head -c 12) ($HEAD_BRANCH)

Identical:      $identical
Cosmetic diff:  $cosmetic_diff  (comment/hash differences only)
Semantic diff:  $semantic_diff  (actual query differences)
Only in base:   $only_base
Only in head:   $only_head

Semantic diffs saved to: $out/smt2_diffs/
EOF

  cat "$out/smt2_summary.txt"
}

# ──────────────────────────────────────────────────────────────
# Phase 7: Generate comparison report
# ──────────────────────────────────────────────────────────────
phase_report() {
  local report="$RESULTS/report.txt"
  info "Generating comparison report..."

  cat > "$report" <<'HEADER'
╔══════════════════════════════════════════════════════════════════════╗
║       Auto-Patterns Benchmarking Report                            ║
╚══════════════════════════════════════════════════════════════════════╝
HEADER

  cat >> "$report" <<EOF

Date:        $(date -u +"%Y-%m-%d %H:%M:%S UTC")
Base branch: $BASE_BRANCH ($(cat "$BASE_DIR/commit.txt" | head -c 12))
Head branch: $HEAD_BRANCH ($(cat "$HEAD_DIR/commit.txt" | head -c 12))
Machine:     $(uname -n) ($(nproc) cores, $(free -h 2>/dev/null | awk '/Mem:/{print $2}' || echo '?') RAM)

════════════════════════════════════════════════════════════════════════
BASELINE ($BASE_BRANCH) — no auto_patterns
════════════════════════════════════════════════════════════════════════

EOF
  cat "$RESULTS/base_metrics.txt" >> "$report"

  cat >> "$report" <<EOF

════════════════════════════════════════════════════════════════════════
HEAD ($HEAD_BRANCH) — with --ext auto_patterns
════════════════════════════════════════════════════════════════════════

EOF
  cat "$RESULTS/head_metrics.txt" >> "$report"

  # Side-by-side comparison
  cat >> "$report" <<EOF

════════════════════════════════════════════════════════════════════════
SIDE-BY-SIDE COMPARISON
════════════════════════════════════════════════════════════════════════

EOF

  printf "%-45s %10s %10s %8s  %10s %10s %8s\n" \
    "File" "Base(s)" "Head(s)" "Δ(%)" "BaseRSS" "HeadRSS" "Δ(%)" >> "$report"
  printf "%s\n" "$(printf '%.0s─' {1..100})" >> "$report"

  # Join base and head metrics for comparison
  paste <(tail -n+3 "$RESULTS/base_metrics.txt" | head -n-3) \
        <(tail -n+3 "$RESULTS/head_metrics.txt" | head -n-3) 2>/dev/null | \
  while IFS=$'\t' read -r base_line head_line; do
    local bname bwall buser bsys brss bq bqs bqf
    local hname hwall huser hsys hrss hq hqs hqf
    read -r bname bwall buser bsys brss bq bqs bqf <<< "$base_line"
    read -r hname hwall huser hsys hrss hq hqs hqf <<< "$head_line"

    # Compute percentage change
    local time_pct rss_pct
    if [ "$bwall" != "?" ] && [ "$hwall" != "?" ] && [ "$bwall" != "0" ]; then
      time_pct=$(echo "scale=1; ($hwall - $bwall) / $bwall * 100" | bc 2>/dev/null || echo "?")
    else
      time_pct="?"
    fi
    if [ "$brss" != "?" ] && [ "$hrss" != "?" ] && [ "$brss" != "0" ]; then
      rss_pct=$(echo "scale=1; ($hrss - $brss) / $brss * 100" | bc 2>/dev/null || echo "?")
    else
      rss_pct="?"
    fi

    printf "%-45s %10s %10s %7s%%  %10s %10s %7s%%\n" \
      "$bname" "$bwall" "$hwall" "$time_pct" "$brss" "$hrss" "$rss_pct" >> "$report"
  done

  # QI profile comparison
  cat >> "$report" <<EOF

════════════════════════════════════════════════════════════════════════
QUANTIFIER INSTANTIATION PROFILES
════════════════════════════════════════════════════════════════════════

--- Baseline ---
EOF
  cat "$RESULTS/base_qi.txt" >> "$report" 2>/dev/null || echo "(no QI data)" >> "$report"

  cat >> "$report" <<EOF

--- Head (auto_patterns) ---
EOF
  cat "$RESULTS/head_qi.txt" >> "$report" 2>/dev/null || echo "(no QI data)" >> "$report"

  # SMT2 diff summary
  if [ -f "$RESULTS/smt2_summary.txt" ]; then
    cat >> "$report" <<EOF

════════════════════════════════════════════════════════════════════════
SMT2 FILE COMPARISON
════════════════════════════════════════════════════════════════════════

EOF
    cat "$RESULTS/smt2_summary.txt" >> "$report"
  fi

  echo "" >> "$report"
  bold "Report written to: $report"
  echo ""
  cat "$report"
}

# ──────────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────────
main() {
  bold "Auto-Patterns Benchmark: $BASE_BRANCH vs $HEAD_BRANCH"
  info "Working directory: $WORKDIR"
  info "Benchmark files: ${#BENCH_FILES[@]}"
  echo ""

  mkdir -p "$WORKDIR" "$RESULTS"

  # Phase 1: Clone
  phase_clone "base" "$BASE_BRANCH" "$BASE_DIR"
  phase_clone "head" "$HEAD_BRANCH" "$HEAD_DIR"

  # Phase 2: Build
  phase_build "base" "$BASE_DIR"
  phase_build "head" "$HEAD_DIR"

  # Phase 3: Run benchmarks
  # Baseline: no auto_patterns
  phase_bench "base" "$BASE_DIR" "$RESULTS/base_bench" ""
  # Head: with auto_patterns
  phase_bench "head" "$HEAD_DIR" "$RESULTS/head_bench" "--ext auto_patterns"

  # Phase 4: Extract metrics
  extract_metrics "base" "$RESULTS/base_bench" "$RESULTS/base_metrics.txt"
  extract_metrics "head" "$RESULTS/head_bench" "$RESULTS/head_metrics.txt"

  # Phase 5: QI profiles
  extract_qi_profile "base" "$RESULTS/base_bench" "$RESULTS/base_qi.txt"
  extract_qi_profile "head" "$RESULTS/head_bench" "$RESULTS/head_qi.txt"

  # Phase 6: SMT2 diffs
  phase_diff_smt2 "$RESULTS/base_bench" "$RESULTS/head_bench" "$RESULTS"

  # Phase 7: Report
  phase_report

  bold "Done! Results in $WORKDIR"
}

main "$@"
