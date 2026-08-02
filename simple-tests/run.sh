#!/usr/bin/env bash
# Run the simplified-effect-system acceptance tests with the stage1 compiler.
#
#   ./simple-tests/run.sh [extra fstar options]
#
# Every file in simple-lib/ and simple-tests/ is expected to verify.  Tests that
# must fail use [@@expect_failure] inside the file itself.

set -u
cd "$(dirname "$0")/.."

FSTAR_EXE=${FSTAR_EXE:-stage1/dune/_build/default/fstarc-full/fstarc1_full.exe}
CACHE_DIR=${CACHE_DIR:-.simple-cache}

if [ ! -x "$FSTAR_EXE" ]; then
  echo "error: $FSTAR_EXE not found; run 'make 1.full' first" >&2
  exit 1
fi

mkdir -p "$CACHE_DIR"

run() {
  FSTAR_LIB="$PWD/simple-lib" "$FSTAR_EXE" \
    --cache_dir "$CACHE_DIR" --no_default_includes \
    --include simple-lib --include simple-tests "$@"
}

failed=0

check() {
  local label=$1; shift
  local out
  out=$("$@" 2>&1)
  if [ $? -eq 0 ]; then
    printf 'PASS %s\n' "$label"
  else
    printf 'FAIL %s\n' "$label"
    printf '%s\n' "$out" | sed 's/^/     /'
    failed=1
  fi
}

# Library and tests must verify.  The library is checked in dependency order so
# that .checked files exist for the extraction tests below.
LIB="simple-lib/Prims.fst
     simple-lib/FStar.Pervasives.Native.fst
     simple-lib/FStar.Attributes.fsti
     simple-lib/FStar.Pervasives.fst
     simple-lib/FStar.Prelude.fsti
     simple-lib/FStar.All.fst
     simple-lib/FStar.Tactics.Effect.fst"

for f in $LIB simple-tests/*.fst; do
  check "$f" run "$@" --cache_checked_modules "$f"
done

# Extraction smoke tests: Div/ML code extracts with --codegen OCaml, and Tac
# code extracts (in direct style) with --codegen Plugin.
ODIR=$(mktemp -d)
check "extract ExtractMe (OCaml)" \
  run "$@" --codegen OCaml --odir "$ODIR" --extract ExtractMe simple-tests/ExtractMe.fst
check "extract TacTest (Plugin)" \
  run "$@" --codegen Plugin --odir "$ODIR" --extract TacTest simple-tests/TacTest.fst
rm -rf "$ODIR"

if [ $failed -eq 0 ]; then
  echo "All simple-tests passed."
else
  echo "Some simple-tests failed." >&2
fi
exit $failed
