---
name: smtprofiling
description: Debug F* queries sent to Z3, diagnosing proof instability and performance issues
---

## Invocation
This skill is used when:
- Verifying F* (.fst) or interface (.fsti) files
- Debugging verification failures and proof performance
- Especially when proofs require high rlimits or fail unpredictably

## Core Operations

### Collect an .smt2 file for problematic proof

Wrap the part of the program to diagnose proof failures with

```fstar
#push-options "--log_queries --z3refresh --query_stats --split_queries always"
let definition_to_be_debugged ...
#pop-options
```

Run F* on the file (with appropriate include paths)

```bash
fstar.exe Module.fst
```

The log messages will show the name of the .smt2 file logged for each proof obligation.

Using `--z3refresh` together with `--log_queries` produces a
self-contained `.smt2` file per query (each query starts with a fresh
Z3 process). This is critical for isolating expensive sub-goals: each
`.smt2` file can be profiled independently.

Using `--split_queries always` decomposes compound VCs into individual
sub-goals. This lets you identify exactly which conjunct of a
proof obligation is expensive. Cross-reference the query number in the
`Query-stats` output with the `.smt2` file number to map each timing
to its isolated file.

### Verify .smt2 file independently of F*

Find `z3` in the path. It might be named `z3-4.13.3`, `z3-4.15.1` etc., with a version number suffix

```bash
z3 queries-myquery.smt2
```

You can add z3 options like `smt.qi.profile=true` to see which quantifiers were firing 
too much and what to do about it

### Interpreting a quantifier profile

The Z3 quantifier profile is printed to stderr. Capture it with:

```bash
z3 smt.qi.profile=true queries-myquery.smt2 2> qi_profile.txt
```

Parse the output to get per-quantifier totals:

```bash
awk '/\[quantifier_instances\]/ {
  name = $2; count = $4; total[name] += count;
} END {
  for (n in total) printf "%8d %s\n", total[n], n;
}' qi_profile.txt | sort -rn | head -20
```

Some quantifiers in F*'s SMT encoding always fire a lot---this is
by design. Typically, quantifiers with unqualified names 
(Box_bool_proj_0) or those with names in Prims, or FStar.
Pervasives will fire a lot.

Look for quantifiers in modules that are in files that you 
authored that are firing a lot---these might signify that you 
should write a pattern for those quantifiers, or control their 
instantiation explicitly.

### Common quantifier cascade patterns

A **quantifier cascade** is when one quantifier instantiation produces
terms that trigger another quantifier, which produces more terms,
creating a positive feedback loop. This is the most common cause of
queries taking minutes instead of seconds.

Signs of a cascade:
- One or two quantifiers have 10,000+ instantiations while everything else has < 100
- Query takes very long wall-clock time but uses modest rlimit
- The dominant quantifier has a single-term pattern like `[SMTPat (f x y)]`
  and its conclusion introduces new terms that match the pattern of
  another quantifier

Example cascade found in EverParse:
1. `cbor_map_equal` unfolds to `forall k. cbor_map_get m1 k == cbor_map_get m2 k`
2. Each `cbor_map_get` produces `cbor_map_defined` terms
3. `cbor_map_defined_alt` has `[SMTPat (cbor_map_defined k f)]` and
   introduces `exists v. cbor_map_mem (k,v) f`
4. Existential skolemization creates new ground terms
5. New terms trigger more pattern matches → 64,000+ instantiations

### Fixing quantifier cascades

**Option 1: Remove the SMTPat and add a `bring_` helper**

Remove `[SMTPat ...]` from the offending lemma. Add a wrapper that
re-introduces the quantifier with its pattern in a controlled scope:

```fstar
// Original: always active, causes cascades
let problematic_lemma (x: t) (y: t)
: Lemma (some_prop x y)
  [SMTPat (f x y)]    // REMOVE THIS
= ...

// New: call bring_ only where needed
let bring_problematic_lemma ()
: Lemma (forall (x: t) (y: t) . {:pattern (f x y)} some_prop x y)
= Classical.forall_intro_2 problematic_lemma
```

Then call `bring_problematic_lemma ()` only in the specific proofs
that need it, rather than polluting all proofs globally.

**Option 2: Use `--using_facts_from` to prune per-function**

Surgically remove a lemma from Z3's context for a specific function
without modifying the lemma itself:

```fstar
#push-options "--using_facts_from '* -Module.Name.problematic_lemma'"
let my_expensive_function ...
#pop-options
```

This is useful for quick experimentation before committing to
Option 1. Verify the quantifier is actually removed by checking the
`.smt2` file.

**Option 3: Use multi-pattern triggers**

Change a single-term pattern to a conjunctive multi-pattern so the
lemma only fires when multiple terms are present:

```fstar
// Before: fires whenever (f x y) appears
[SMTPat (f x y)]

// After: fires only when both (f x y) AND (g x) are present
[SMTPat (f x y); SMTPat (g x)]
```

### Systematic profiling workflow

For large projects, profile the entire build:

```bash
# 1. Full build with --query_stats
make -j$(nproc) OTHERFLAGS="--query_stats" 2>&1 | tee build_profile.log

# 2. Find top files by SMT time
grep -a "Query-stats" build_profile.log | grep "succeeded" \
  | sed -n 's/(\([^(]*\)\.\(fst\|fsti\)([^)]*)).*succeeded in \([0-9]*\) milliseconds.*/\1.\2 \3/p' \
  | awk '{f[$1]+=$2} END {for(k in f) print f[k], k}' | sort -rn | head -20

# 3. Find top individual queries
grep -a "Query-stats" build_profile.log | grep "succeeded" \
  | sed -n 's/.*Query-stats (\([^)]*\)).*succeeded in \([0-9]*\) milliseconds.*rlimit \([0-9]*\) (used rlimit \([0-9.]*\)).*/\2\t\4\t\3\t\1/p' \
  | sort -rn | head -20

# 4. For the most expensive query, isolate it:
#push-options "--log_queries --z3refresh --query_stats --split_queries always"

# 5. Profile the isolated .smt2 file:
z3 smt.qi.profile=true queries-Module-NNN.smt2 2> qi_profile.txt

# 6. Parse the profile to find the dominant quantifier(s)
```

### F* options for controlling SMT performance

| Option | Effect |
|--------|--------|
| `--split_queries always` | Each assertion becomes its own Z3 query |
| `--z3refresh` | Fresh Z3 process per query (no accumulated state) |
| `--log_queries` | Write `.smt2` files for each query |
| `--query_stats` | Print per-query timing and rlimit usage |
| `--z3cliopt smt.arith.nl=false` | Disable non-linear arithmetic |
| `--z3cliopt smt.qi.eager_threshold=N` | Limit quantifier instantiation eagerness |
| `--using_facts_from '* -Name'` | Prune specific lemmas from Z3 context |
| `--ext context_pruning` | Prune unreachable assumptions (default on) |
| `--fuel N` / `--ifuel N` | Control recursive unfolding depth |

### Tightening fuel, ifuel, and rlimit

After fixing expensive queries, tighten the settings:
- Reduce `fuel` and `ifuel` to the minimum that works (prefer 0-2)
- Reduce `rlimit` to 2-4x the `used rlimit` reported by `--query_stats`
- High fuel (>2) causes exponential unfolding; replace with explicit lemma calls
- High ifuel (>2) causes excessive inversion; add explicit match/inversion steps

### More information on SMT profiling

Find the directory PoP-in-FStar on the local machine, or locate it here:
https://github.com/FStarLang/PoP-in-FStar

See https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html#profiling-z3-and-solving-proof-performance-issues

The section under_the_hood/uth_smt.rst contains information about F*'s SMT
encoding and how to profile.
