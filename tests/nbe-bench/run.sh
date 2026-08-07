#!/usr/bin/env bash
# Benchmark the call-by-name normalizer (FStarC.TypeChecker.Normalize) against
# the call-by-value NBE evaluator (FStarC.TypeChecker.NBE).
#
#   ./run.sh [fstar.exe] [reps]
#
# Each module is checked twice per rep: once with the default engine and once
# with --use_nbe true, which routes every explicit norm request (assert_norm,
# normalize_term, norm [..]) through NBE. We report the best of `reps` runs,
# since the machine is usually shared and only the minimum is meaningful.
#
# Bench.Empty measures process startup + Prims/FStar loading; it is subtracted
# from every other module to get the "net" normalization time.
set -u

HERE=$(cd "$(dirname "$0")" && pwd)
FSTAR=${1:-$HERE/../../out/bin/fstar.exe}
REPS=${2:-5}

# Bench.SymTac*, which measure the tactic-level norm_term path, are handled
# separately below: they pick their engine with the [nbe] norm step rather
# than with --use_nbe, so they cannot be run as a flag flip.
MODS="Bench.Empty Bench.Arith Bench.List Bench.Sort Bench.Tree Bench.MachInt Bench.HO Bench.Share Bench.Dead Bench.Sym"

run1() { # $1 = file, $2.. = extra flags; echoes elapsed ms, or nothing on failure
  local f=$1; shift
  local s e
  s=$(date +%s%N)
  timeout 900 "$FSTAR" --cache_off "$@" "$f" >/dev/null 2>&1 || return 1
  e=$(date +%s%N)
  echo $(( (e - s) / 1000000 ))
}

best() { # $1 = file, $2.. = extra flags
  local f=$1; shift
  local b=999999999 t
  for _ in $(seq "$REPS"); do
    t=$(run1 "$f" "$@") || continue
    [ "$t" -lt "$b" ] && b=$t
  done
  [ "$b" = 999999999 ] && return 1
  echo "$b"
}

cd "$HERE"

declare -A N B
for m in $MODS; do
  N[$m]=$(best "$m.fst")               || { echo "FAILED (norm): $m" >&2; N[$m]=0; }
  B[$m]=$(best "$m.fst" --use_nbe true) || { echo "FAILED (nbe): $m" >&2; B[$m]=0; }
done

base_n=${N[Bench.Empty]}
base_b=${B[Bench.Empty]}

echo "# best of $REPS, wall clock ms; net = total minus the Bench.Empty startup baseline"
printf "%-16s %9s %9s %9s %9s %8s\n" module norm_ms nbe_ms net_norm net_nbe speedup
for m in $MODS; do
  if [ "$m" = Bench.Empty ]; then
    printf "%-16s %9s %9s %9s %9s %8s\n" "$m" "${N[$m]}" "${B[$m]}" - - -
    continue
  fi
  nn=$(( ${N[$m]} - base_n )); [ $nn -lt 1 ] && nn=1
  nb=$(( ${B[$m]} - base_b )); [ $nb -lt 1 ] && nb=1
  sp=$(awk -v a=$nn -v b=$nb 'BEGIN{printf "%.1fx", a/b}')
  printf "%-16s %9s %9s %9s %9s %8s\n" "$m" "${N[$m]}" "${B[$m]}" "$nn" "$nb" "$sp"
done

# Tactic-level norm_term on an open term. The engine is chosen by the [nbe]
# norm step inside the module, so these are three distinct modules rather
# than one module under two flags.
echo
sb=$(best Bench.SymTacBase.fst) || sb=0
sn=$(best Bench.SymTac.fst)     || sn=0
se=$(best Bench.SymTacNbe.fst)  || se=0
nn=$(( sn - sb )); [ $nn -lt 1 ] && nn=1
nb=$(( se - sb )); [ $nb -lt 1 ] && nb=1
echo "# tactic-level norm_term on an open term (baseline = Bench.SymTacBase)"
printf "%-16s %9s %9s %9s %9s %8s\n" module norm_ms nbe_ms net_norm net_nbe speedup
printf "%-16s %9s %9s %9s %9s %8s\n" Bench.SymTac "$sn" "$se" "$nn" "$nb" \
  "$(awk -v a=$nn -v b=$nb 'BEGIN{printf "%.1fx", a/b}')"
