#!/usr/bin/env bash
#
# diff_smt2.sh — Differential verification between two F* branches
#
# This script:
#   1. Clones the FStar repo twice (base and head branches)
#   2. Builds stage2 for both from scratch
#   3. Verifies ulib, tests, examples, and doc with --log_queries
#   4. Collects all .smt2 and .checked files into a results directory
#   5. Compares .checked files byte-for-byte
#   6. Compares .smt2 files, stripping version/commit/hash metadata
#
# Usage:
#   ./tools/diff_smt2.sh [WORKDIR] [BASE_BRANCH] [HEAD_BRANCH]
#
# WORKDIR      defaults to /tmp/fstar-diff-<timestamp>
# BASE_BRANCH  defaults to fstar2
# HEAD_BRANCH  defaults to fstar2_nomlish
#
# The script is idempotent: re-running skips completed phases.
# Each phase writes a sentinel (.done) file on success.
#
# Requirements: git, GNU make, OCaml toolchain (opam), ~30 GB disk, ~2 h wall time
#
set -euo pipefail

REPO_URL="https://github.com/FStarLang/FStar.git"
BASE_BRANCH="${2:-fstar2}"
HEAD_BRANCH="${3:-fstar2_nomlish}"

WORKDIR="${1:-/tmp/fstar-diff-$(date +%s)}"
BASE_DIR="$WORKDIR/base"
HEAD_DIR="$WORKDIR/head"
RESULTS="$WORKDIR/results"

NPROC=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

bold()  { printf '\033[1m%s\033[0m\n' "$*"; }
info()  { printf '==> %s\n' "$*"; }
error() { printf 'ERROR: %s\n' "$*" >&2; }

mkdir -p "$WORKDIR" "$RESULTS"

# ──────────────────────────────────────────────────
# Phase 1: Clone
# ──────────────────────────────────────────────────
phase_clone() {
  local label=$1 branch=$2 dir=$3
  if [ -d "$dir/.git" ]; then
    info "[$label] Already cloned at $dir, fetching..."
    git -C "$dir" fetch origin "$branch"
    git -C "$dir" checkout "$branch"
    git -C "$dir" reset --hard "origin/$branch"
  else
    info "[$label] Cloning $REPO_URL branch=$branch into $dir"
    git clone --branch "$branch" --single-branch "$REPO_URL" "$dir"
  fi
  git -C "$dir" rev-parse HEAD > "$dir/commit.txt"
  info "[$label] HEAD = $(git -C "$dir" rev-parse --short HEAD)"
}

# ──────────────────────────────────────────────────
# Phase 2: Build (stage2 + full compiler)
# ──────────────────────────────────────────────────
phase_build() {
  local label=$1 dir=$2
  if [ -x "$dir/stage2/out/bin/fstar.exe" ]; then
    info "[$label] stage2/out/bin/fstar.exe already exists, skipping build"
    return 0
  fi
  info "[$label] Building stage2 (this takes ~30 min)..."
  make -C "$dir" stage2 -j"$NPROC" 2>&1 | tail -5
  if [ ! -x "$dir/stage2/out/bin/fstar.exe" ]; then
    error "[$label] Build failed — no fstar.exe produced"
    return 1
  fi
  info "[$label] Build OK"
}

# ──────────────────────────────────────────────────
# Phase 3: Verify with --log_queries
# ──────────────────────────────────────────────────
phase_verify() {
  local label=$1 dir=$2 done_file=$3
  local fstar_exe="$dir/stage2/out/bin/fstar.exe"

  if [ -f "$done_file" ]; then
    info "[$label] Verification already done (found $done_file), skipping"
    return 0
  fi

  # Clean up any stale .smt2 files so we only collect fresh ones
  info "[$label] Cleaning stale .smt2 files..."
  find "$dir" -name 'queries-*.smt2' -delete 2>/dev/null || true

  # ── ulib ──
  # Re-verify ulib with --log_queries into a fresh cache dir so that
  # fstar.exe actually re-checks (the stage2 build already checked
  # ulib, but without --log_queries).
  info "[$label] Verifying ulib with --log_queries ..."
  mkdir -p "$dir/_diff_cache/ulib.checked" "$dir/_diff_cache/ulib.ml"
  env \
    SRC="$dir/ulib/" \
    FSTAR_EXE="$fstar_exe" \
    CACHE_DIR="$dir/_diff_cache/ulib.checked/" \
    OUTPUT_DIR="$dir/_diff_cache/ulib.ml/" \
    CODEGEN=OCaml \
    TAG=lib \
    OTHERFLAGS="--log_queries" \
    TOUCH="$dir/_diff_cache/.ulib.touch" \
    make -C "$dir" -f mk/lib.mk verify -skj"$NPROC" 2>&1 | tail -3 || true

  # ── tests, examples ──
  for sub in tests examples; do
    info "[$label] Verifying $sub with --log_queries ..."
    OTHERFLAGS="--log_queries" \
      make -C "$dir/$sub" all \
        FSTAR_EXE="$fstar_exe" -skj"$NPROC" 2>&1 | tail -3 || true
  done

  # ── doc ──
  info "[$label] Verifying doc with --log_queries ..."
  OTHERFLAGS="--log_queries" \
    make -C "$dir" _doc \
      FSTAR_EXE="$fstar_exe" -skj"$NPROC" 2>&1 | tail -3 || true

  # ── Fixup: re-run native-plugin tests in interpreted mode ──
  # Tests like tests/semiring run both interpreted and native modes.
  # When make -j runs both in parallel, the two fstar.exe invocations
  # race on the same queries-*.smt2 file, producing non-deterministic
  # output.  Additionally, native plugin mode may avoid SMT entirely
  # (tactic handles everything natively), so no smt2 file is written.
  # To get deterministic, reproducible smt2 output, re-run these tests
  # in interpreted mode only (without --load_cmxs), which is what we
  # actually want to compare.
  for rerun_dir in "$dir/tests/semiring"; do
    if [ -d "$rerun_dir" ]; then
      info "[$label] Re-verifying $(basename "$rerun_dir") in interpreted mode ..."
      find "$rerun_dir" -name 'queries-*.Test.smt2' -delete 2>/dev/null || true
      for testfile in "$rerun_dir"/*.Test.fst; do
        [ -f "$testfile" ] || continue
        info "[$label]   $(basename "$testfile")"
        "$fstar_exe" --log_queries --already_cached 'Prims,FStar' \
          "$testfile" 2>&1 | tail -2 || true
      done
    fi
  done

  touch "$done_file"
  info "[$label] Verification phase complete"
}

# ──────────────────────────────────────────────────
# Phase 4: Collect artifacts (.smt2 + .checked)
# ──────────────────────────────────────────────────
phase_collect() {
  local label=$1 dir=$2 out_dir=$3

  if [ -f "$out_dir/.done" ]; then
    info "[$label] Collection already done (found $out_dir/.done), skipping"
    return 0
  fi

  mkdir -p "$out_dir/smt2" "$out_dir/checked"

  # ── Collect .smt2 files ──
  # Preserve relative paths (/ → __) as flat keys so base and head can
  # be compared file-by-file.
  info "[$label] Collecting .smt2 files ..."
  # Exclude IDE test directories: multiple .in files race on the same
  # queries-*.smt2 under make -j, producing non-deterministic output.
  find "$dir" -name 'queries-*.smt2' \
       -not -path '*/_build/*' \
       -not -path '*/tools/*' \
       -not -path '*/stage0/*' \
       -not -path '*/stage1/*' \
       -not -path '*/tests/ide/*' \
    | while IFS= read -r f; do
        relpath="${f#$dir/}"
        key="$(echo "$relpath" | tr '/' '__')"
        cp "$f" "$out_dir/smt2/$key"
      done

  local smt2_count
  smt2_count=$(find "$out_dir/smt2" -name '*.smt2' | wc -l)
  info "[$label] Collected $smt2_count .smt2 files"

  # ── Collect .checked files ──
  # Gather every .checked file produced during stage2 build + the
  # --log_queries re-verification (ulib, tests, examples, doc).
  # Skip stage0/stage1 to avoid bootstrap noise.
  info "[$label] Collecting .checked files ..."
  find "$dir" -name '*fst.checked' -or -name "*.fsti.checked" \
       -not -path '*/stage0/*' \
       -not -path '*/stage1/*' \
       -not -path '*/_build/*' \
    | while IFS= read -r f; do
        relpath="${f#$dir/}"
        key="$(echo "$relpath" | tr '/' '__')"
        cp "$f" "$out_dir/checked/$key"
      done

  local checked_count
  checked_count=$(find "$out_dir/checked" -type f | wc -l)
  info "[$label] Collected $checked_count .checked files"

  touch "$out_dir/.done"
}

# ──────────────────────────────────────────────────
# Phase 5: Compare .checked files
# ──────────────────────────────────────────────────
phase_compare_checked() {
  local base_dir="$1" head_dir="$2" out="$3"

  info "Comparing .checked files..."

  local base_list="$out/checked_base_list.txt"
  local head_list="$out/checked_head_list.txt"
  ls "$base_dir" | sort > "$base_list"
  ls "$head_dir" | sort > "$head_list"

  comm -23 "$base_list" "$head_list" > "$out/checked_only_in_base.txt"
  comm -13 "$base_list" "$head_list" > "$out/checked_only_in_head.txt"
  comm -12 "$base_list" "$head_list" > "$out/checked_common.txt"

  local total_base total_head common only_base only_head
  total_base=$(wc -l < "$base_list")
  total_head=$(wc -l < "$head_list")
  common=$(wc -l < "$out/checked_common.txt")
  only_base=$(wc -l < "$out/checked_only_in_base.txt")
  only_head=$(wc -l < "$out/checked_only_in_head.txt")

  local identical=0 different=0
  : > "$out/checked_different.txt"

  while IFS= read -r f; do
    if cmp -s "$base_dir/$f" "$head_dir/$f"; then
      identical=$((identical + 1))
    else
      different=$((different + 1))
      local bsz hsz
      bsz=$(stat -c%s "$base_dir/$f" 2>/dev/null || stat -f%z "$base_dir/$f")
      hsz=$(stat -c%s "$head_dir/$f" 2>/dev/null || stat -f%z "$head_dir/$f")
      echo "$f  base=$bsz  head=$hsz" >> "$out/checked_different.txt"
    fi
  done < "$out/checked_common.txt"

  # ── Summary ──
  cat > "$out/checked_summary.txt" <<EOF
=== Differential .checked Comparison ===
Date:        $(date -u +"%Y-%m-%d %H:%M:%S UTC")
Base branch: $BASE_BRANCH ($(cat "$BASE_DIR/commit.txt" | head -c 12))
Head branch: $HEAD_BRANCH ($(cat "$HEAD_DIR/commit.txt" | head -c 12))

Files in base:     $total_base
Files in head:     $total_head
Common files:      $common
Only in base:      $only_base
Only in head:      $only_head

Byte-identical:    $identical
Different:         $different
EOF

  if [ "$different" -gt 0 ]; then
    {
      echo ""
      echo "=== Different .checked files ==="
      cat "$out/checked_different.txt"
    } >> "$out/checked_summary.txt"
  fi

  if [ "$only_base" -gt 0 ]; then
    {
      echo ""
      echo "=== .checked files only in base ==="
      cat "$out/checked_only_in_base.txt"
    } >> "$out/checked_summary.txt"
  fi

  if [ "$only_head" -gt 0 ]; then
    {
      echo ""
      echo "=== .checked files only in head ==="
      cat "$out/checked_only_in_head.txt"
    } >> "$out/checked_summary.txt"
  fi

  echo ""
  cat "$out/checked_summary.txt"
  echo ""
  if [ "$different" -eq 0 ] && [ "$only_base" -eq 0 ] && [ "$only_head" -eq 0 ]; then
    bold "✅ CHECKED: All $identical .checked files are byte-identical"
  else
    bold "❌ CHECKED: $different files differ, $only_base base-only, $only_head head-only"
  fi
}

# ──────────────────────────────────────────────────
# Phase 6: Compare .smt2 files
# ──────────────────────────────────────────────────
#
# We strip / normalise patterns that are expected to differ:
#   - ; ...          comment-only lines (version, commit hash, captions)
#   - uu___NNN       gensym-generated universe variable names
#   - Non_total_Tm_arrow_HEX  MD5-hash–based arrow-type names
#   - Tm_refine_HEX  MD5-hash–based refinement-type names
#   - Tm_arrow_HEX   MD5-hash–based arrow-type names
#
# Everything else — (push), (pop), (assert ...), (check-sat), (declare-fun ...),
# etc. — must be identical between base and head.
#
strip_metadata() {
  sed -E \
    -e '/^;/d' \
    -e 's/uu___[0-9]+/uu___NNN/g' \
    -e 's/Non_total_Tm_arrow_[a-f0-9]+/Non_total_Tm_arrow_HASH/g' \
    -e 's/Tm_refine_[a-f0-9]+/Tm_refine_HASH/g' \
    -e 's/Tm_arrow_[a-f0-9]+/Tm_arrow_HASH/g' \
    "$1"
}

phase_compare_smt2() {
  local base_smt2="$1" head_smt2="$2" out="$3"

  info "Comparing .smt2 files..."

  local base_list="$out/smt2_base_list.txt"
  local head_list="$out/smt2_head_list.txt"
  ls "$base_smt2" | sort > "$base_list"
  ls "$head_smt2" | sort > "$head_list"

  comm -23 "$base_list" "$head_list" > "$out/smt2_only_in_base.txt"
  comm -13 "$base_list" "$head_list" > "$out/smt2_only_in_head.txt"
  comm -12 "$base_list" "$head_list" > "$out/smt2_common.txt"

  local total_base total_head common only_base only_head
  total_base=$(wc -l < "$base_list")
  total_head=$(wc -l < "$head_list")
  common=$(wc -l < "$out/smt2_common.txt")
  only_base=$(wc -l < "$out/smt2_only_in_base.txt")
  only_head=$(wc -l < "$out/smt2_only_in_head.txt")

  local identical=0 semantic_diff=0 cosmetic_diff=0
  : > "$out/smt2_semantic_diffs.txt"
  : > "$out/smt2_cosmetic_diffs.txt"
  mkdir -p "$out/smt2_diffs"

  while IFS= read -r f; do
    bf="$base_smt2/$f"
    hf="$head_smt2/$f"

    if diff -q "$bf" "$hf" >/dev/null 2>&1; then
      identical=$((identical + 1))
    else
      # Check if difference is only in metadata (comment lines)
      if diff <(strip_metadata "$bf") <(strip_metadata "$hf") >/dev/null 2>&1; then
        cosmetic_diff=$((cosmetic_diff + 1))
        echo "$f" >> "$out/smt2_cosmetic_diffs.txt"
      else
        semantic_diff=$((semantic_diff + 1))
        echo "$f" >> "$out/smt2_semantic_diffs.txt"
        # Save the actual diff for inspection
        diff -u <(strip_metadata "$bf") <(strip_metadata "$hf") \
          > "$out/smt2_diffs/${f}.diff" 2>&1 || true
      fi
    fi
  done < "$out/smt2_common.txt"

  # ── Summary ──
  cat > "$out/smt2_summary.txt" <<EOF
=== Differential SMT2 Comparison ===
Date:        $(date -u +"%Y-%m-%d %H:%M:%S UTC")
Base branch: $BASE_BRANCH ($(cat "$BASE_DIR/commit.txt" | head -c 12))
Head branch: $HEAD_BRANCH ($(cat "$HEAD_DIR/commit.txt" | head -c 12))

Files in base:     $total_base
Files in head:     $total_head
Common files:      $common
Only in base:      $only_base
Only in head:      $only_head

Byte-identical:    $identical
Cosmetic diff:     $cosmetic_diff  (comment lines only — captions, version, commit hash)
Semantic diff:     $semantic_diff  (actual SMT2 content differs)
EOF

  if [ "$semantic_diff" -gt 0 ]; then
    {
      echo ""
      echo "=== Files with SEMANTIC differences ==="
      cat "$out/smt2_semantic_diffs.txt"
    } >> "$out/smt2_summary.txt"
  fi

  if [ "$cosmetic_diff" -gt 0 ]; then
    {
      echo ""
      echo "=== Files with cosmetic differences (comment lines only) ==="
      cat "$out/smt2_cosmetic_diffs.txt"
    } >> "$out/smt2_summary.txt"
  fi

  if [ "$only_base" -gt 0 ]; then
    {
      echo ""
      echo "=== .smt2 files only in base ==="
      cat "$out/smt2_only_in_base.txt"
    } >> "$out/smt2_summary.txt"
  fi

  if [ "$only_head" -gt 0 ]; then
    {
      echo ""
      echo "=== .smt2 files only in head ==="
      cat "$out/smt2_only_in_head.txt"
    } >> "$out/smt2_summary.txt"
  fi

  echo ""
  cat "$out/smt2_summary.txt"
  echo ""
  if [ "$semantic_diff" -eq 0 ] && [ "$only_base" -eq 0 ] && [ "$only_head" -eq 0 ]; then
    bold "✅ SMT2: No semantic differences across all $common files"
  else
    bold "❌ SMT2: $semantic_diff semantic diffs, $only_base base-only, $only_head head-only"
    if [ "$semantic_diff" -gt 0 ]; then
      bold "   Diffs saved to: $out/smt2_diffs/"
    fi
  fi
}

# ──────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────
bold "================================================================"
bold " Differential Verification: .checked + .smt2"
bold " Base: $BASE_BRANCH  |  Head: $HEAD_BRANCH"
bold " Work dir: $WORKDIR"
bold "================================================================"
echo ""

info "Phase 1/6: Clone repositories"
phase_clone "base" "$BASE_BRANCH" "$BASE_DIR"
phase_clone "head" "$HEAD_BRANCH" "$HEAD_DIR"
echo ""

info "Phase 2/6: Build both branches"
phase_build "base" "$BASE_DIR"
phase_build "head" "$HEAD_DIR"
echo ""

info "Phase 3/6: Verify with --log_queries"
phase_verify "base" "$BASE_DIR" "$RESULTS/.verify_base_done"
echo ""
phase_verify "head" "$HEAD_DIR" "$RESULTS/.verify_head_done"
echo ""

info "Phase 4/6: Collect .smt2 and .checked files"
phase_collect "base" "$BASE_DIR" "$RESULTS/base"
phase_collect "head" "$HEAD_DIR" "$RESULTS/head"
echo ""

info "Phase 5/6: Compare .checked files"
phase_compare_checked "$RESULTS/base/checked" "$RESULTS/head/checked" "$RESULTS"
echo ""

info "Phase 6/6: Compare .smt2 files"
phase_compare_smt2 "$RESULTS/base/smt2" "$RESULTS/head/smt2" "$RESULTS"
echo ""

bold "================================================================"
bold " All results in: $RESULTS/"
bold " .checked summary: $RESULTS/checked_summary.txt"
bold " .smt2 summary:    $RESULTS/smt2_summary.txt"
bold " .smt2 diffs:      $RESULTS/smt2_diffs/"
bold " Collected files:  $RESULTS/base/  $RESULTS/head/"
bold "================================================================"
