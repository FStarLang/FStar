#!/usr/bin/env bash
#
# diff_smt2.sh — Differential SMT2 verification between fstar2 and fstar2_nomlish
#
# This script:
#   1. Clones the FStar repo twice (base = fstar2, head = fstar2_nomlish)
#   2. Builds both from scratch
#   3. Verifies ulib, tests, examples, and doc with --log_queries
#   4. Collects all .smt2 files
#   5. Compares them, stripping version/commit/hash metadata
#
# Usage:
#   ./tools/diff_smt2.sh [WORKDIR]
#
# WORKDIR defaults to /tmp/fstar-diff-$(date +%s)
# The script is idempotent on each phase; re-running skips completed phases.
#
# Requirements: git, GNU make, OCaml toolchain (opam), ~30GB disk, ~2h wall time
#
set -euo pipefail

REPO_URL="https://github.com/FStarLang/FStar.git"
BASE_BRANCH="fstar2"
HEAD_BRANCH="fstar2_nomlish"

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
# Phase 3: Verify with --log_queries, collect .smt2
# ──────────────────────────────────────────────────
phase_verify() {
  local label=$1 dir=$2 smt2_dir=$3
  local fstar_exe="$dir/stage2/out/bin/fstar.exe"

  if [ -f "$smt2_dir/.done" ]; then
    info "[$label] Verification already done (found $smt2_dir/.done), skipping"
    return 0
  fi

  mkdir -p "$smt2_dir"

  # Clean up any stale .smt2 files so we only collect fresh ones
  info "[$label] Cleaning stale .smt2 files..."
  find "$dir" -name 'queries-*.smt2' -delete 2>/dev/null || true

  # ── ulib ──
  # Re-verify ulib with --log_queries. We use a temporary cache dir
  # so that fstar.exe actually re-verifies (the stage2 build already
  # checked ulib, but without --log_queries).
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

  # ── tests, examples, doc ──
  # These are run via the top-level Makefile's _test target which
  # invokes make in tests/, examples/, and doc/ subdirectories.
  for sub in tests examples; do
    info "[$label] Verifying $sub with --log_queries ..."
    OTHERFLAGS="--log_queries" \
      make -C "$dir/$sub" all \
        FSTAR_EXE="$fstar_exe" -skj"$NPROC" 2>&1 | tail -3 || true
  done

  info "[$label] Verifying doc with --log_queries ..."
  OTHERFLAGS="--log_queries" \
    make -C "$dir" _doc \
      FSTAR_EXE="$fstar_exe" -skj"$NPROC" 2>&1 | tail -3 || true

  # ── Collect .smt2 files ──
  # We find all queries-*.smt2 files in the tree and copy them into
  # the output directory, preserving relative paths as keys so that
  # base and head can be compared file-by-file.
  info "[$label] Collecting .smt2 files ..."
  find "$dir" -name 'queries-*.smt2' \
       -not -path '*/_build/*' \
       -not -path '*/tools/*' \
    | while IFS= read -r f; do
        relpath="${f#$dir/}"
        destdir="$smt2_dir/$(dirname "$relpath")"
        mkdir -p "$destdir"
        cp "$f" "$destdir/"
      done

  local count
  count=$(find "$smt2_dir" -name '*.smt2' | wc -l)
  info "[$label] Collected $count .smt2 files total"
  touch "$smt2_dir/.done"
}

# ──────────────────────────────────────────────────
# Phase 4: Compare .smt2 files
# ──────────────────────────────────────────────────
#
# We strip lines that are expected to differ:
#   - ; F* version:  (version string)
#   - ; commit=      (git commit hash)
#   - ;              (comment-only lines: captions, timestamps, etc.)
#
# Everything else — (push), (pop), (assert ...), (check-sat), (declare-fun ...),
# etc. — must be identical between base and head.
#
strip_metadata() {
  sed -E \
    -e '/^;/d' \
    "$1"
}

phase_compare() {
  local base_smt2="$1" head_smt2="$2" out="$3"

  info "Comparing .smt2 files..."

  local base_files head_files
  base_files=$(cd "$base_smt2" && find . -name '*.smt2' | sort)
  head_files=$(cd "$head_smt2" && find . -name '*.smt2' | sort)

  # Files only in base / only in head / in common
  comm -23 <(echo "$base_files") <(echo "$head_files") > "$out/only_in_base.txt"
  comm -13 <(echo "$base_files") <(echo "$head_files") > "$out/only_in_head.txt"
  comm -12 <(echo "$base_files") <(echo "$head_files") > "$out/common_files.txt"

  local total_base total_head common only_base only_head
  local identical=0 semantic_diff=0 cosmetic_diff=0

  total_base=$(echo "$base_files" | grep -c . || true)
  total_head=$(echo "$head_files" | grep -c . || true)
  common=$(wc -l < "$out/common_files.txt")
  only_base=$(wc -l < "$out/only_in_base.txt")
  only_head=$(wc -l < "$out/only_in_head.txt")

  : > "$out/semantic_diffs.txt"
  : > "$out/cosmetic_diffs.txt"
  mkdir -p "$out/diffs"

  while IFS= read -r f; do
    bf="$base_smt2/$f"
    hf="$head_smt2/$f"

    if diff -q "$bf" "$hf" >/dev/null 2>&1; then
      identical=$((identical + 1))
    else
      # Check if difference is only in metadata (comment lines)
      if diff <(strip_metadata "$bf") <(strip_metadata "$hf") >/dev/null 2>&1; then
        cosmetic_diff=$((cosmetic_diff + 1))
        echo "$f" >> "$out/cosmetic_diffs.txt"
      else
        semantic_diff=$((semantic_diff + 1))
        echo "$f" >> "$out/semantic_diffs.txt"
        # Save the actual diff for inspection
        mkdir -p "$out/diffs/$(dirname "$f")"
        diff -u <(strip_metadata "$bf") <(strip_metadata "$hf") \
          > "$out/diffs/${f}.diff" 2>&1 || true
      fi
    fi
  done < "$out/common_files.txt"

  # ── Summary ──
  cat > "$out/summary.txt" <<EOF
=== Differential SMT2 Comparison ===
Date:        $(date -u +"%Y-%m-%d %H:%M:%S UTC")
Base branch: $BASE_BRANCH ($(git -C "$BASE_DIR" rev-parse --short HEAD))
Head branch: $HEAD_BRANCH ($(git -C "$HEAD_DIR" rev-parse --short HEAD))

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
      cat "$out/semantic_diffs.txt"
    } >> "$out/summary.txt"
  fi

  if [ "$cosmetic_diff" -gt 0 ]; then
    {
      echo ""
      echo "=== Files with cosmetic differences (comment lines only) ==="
      cat "$out/cosmetic_diffs.txt"
    } >> "$out/summary.txt"
  fi

  if [ "$only_base" -gt 0 ]; then
    {
      echo ""
      echo "=== Files only in base ==="
      cat "$out/only_in_base.txt"
    } >> "$out/summary.txt"
  fi

  if [ "$only_head" -gt 0 ]; then
    {
      echo ""
      echo "=== Files only in head ==="
      cat "$out/only_in_head.txt"
    } >> "$out/summary.txt"
  fi

  # Print to terminal
  echo ""
  cat "$out/summary.txt"
  echo ""
  if [ "$semantic_diff" -eq 0 ]; then
    bold "✅ SUCCESS: No semantic differences in SMT2 output"
  else
    bold "❌ FAILURE: $semantic_diff files have semantic SMT2 differences"
    bold "   Diffs saved to: $out/diffs/"
  fi
}

# ──────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────
bold "================================================================"
bold " Differential SMT2 Verification"
bold " Base: $BASE_BRANCH  |  Head: $HEAD_BRANCH"
bold " Work dir: $WORKDIR"
bold "================================================================"
echo ""

info "Phase 1/4: Clone repositories"
phase_clone "base" "$BASE_BRANCH" "$BASE_DIR"
phase_clone "head" "$HEAD_BRANCH" "$HEAD_DIR"
echo ""

info "Phase 2/4: Build both branches"
phase_build "base" "$BASE_DIR"
phase_build "head" "$HEAD_DIR"
echo ""

info "Phase 3/4: Verify with --log_queries and collect .smt2 files"
phase_verify "base" "$BASE_DIR" "$RESULTS/base_smt2"
echo ""
phase_verify "head" "$HEAD_DIR" "$RESULTS/head_smt2"
echo ""

info "Phase 4/4: Compare .smt2 output"
phase_compare "$RESULTS/base_smt2" "$RESULTS/head_smt2" "$RESULTS"
echo ""

bold "All results in: $RESULTS/"
bold "Summary:        $RESULTS/summary.txt"
