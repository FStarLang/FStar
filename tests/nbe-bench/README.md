# Normalizer vs NBE benchmarks

F* has two reduction engines:

* `FStarC.TypeChecker.Normalize` — call-by-name with memoization. This is the
  **reference** behaviour; anything the two engines disagree on is an NBE bug.
* `FStarC.TypeChecker.NBE` — normalization by evaluation, call-by-value.

This directory measures the tradeoff between them. Every module here is also a
differential test: each `assert_norm` is checked under `--no_smt`, so it only
succeeds if the engine in use actually computed the right value.

## Running

```
make                                        # check every module (default engine)
make OTHERFLAGS="--use_nbe true"            # check every module through NBE
make bench                                  # timing harness, best of 5
make bench REPS=9                           # more repetitions
```

`run.sh` reports the best of N runs and subtracts `Bench.Empty` (process
startup and `Prims`/`FStar` loading, ~2.9 s) to get the `net` column. The
minimum is the only meaningful statistic on a shared machine.

## Selecting the engine

`--use_nbe true` sets `nbe_step` in the ambient cfg
(`Cfg.add_nbe`), which `Normalize.handle_norm_request` turns into an `NBE` step
for every *explicit* norm request encountered while normalizing — `assert_norm`,
`normalize_term`, `norm [..]`, `norm_spec`, and library preconditions such as
`FStar.Calc.calc_finish`'s. That is what `Bench.Arith` … `Bench.Sym` exercise.

It does **not** affect tactic-level `norm_term`, which calls
`Normalize.normalize` directly and so never passes through
`handle_norm_request`. To benchmark that path the engine has to be selected with
the explicit `nbe` norm step, which is why `Bench.SymTac` (normalizer),
`Bench.SymTacNbe` (NBE) and `Bench.SymTacBase` (no normalization) are three
separate modules rather than one module under two flags.

The two other engine switches are not covered here:
`--use_nbe_for_extraction true` (measured separately: extracting all of `ulib`
takes 84.7 s with the normalizer and 85.0 s with NBE, producing byte-identical
output) and `--__tactics_nbe`, which is currently broken because `TAC` is a
layered effect that NBE cannot reify.

## What each module measures

| module | kernel |
|---|---|
| `Bench.Empty` | nothing; the startup baseline subtracted from all others |
| `Bench.Arith` | `fib 24`, `ack 2 6` — closed first-order arithmetic recursion |
| `Bench.List` | `map`/`filter`/`append`/`rev`/`sum` over ~800-element lists |
| `Bench.Sort` | insertion sort of 250 elements, then a sortedness check |
| `Bench.Tree` | build and sum a complete binary tree of depth 12 |
| `Bench.MachInt` | 2000 iterations of `UInt32` `+%^`/`*%^` — dominated by primops |
| `Bench.HO` | 400-fold function composition, and `fold_left` over 600 elements |
| `Bench.Share` | one expensive `let` used four times — rewards memoization |
| `Bench.Dead` | an expensive argument that is discarded — rewards laziness |
| `Bench.Sym` | norm request under a binder: the result is a 20000-node *residual* term |
| `Bench.SymTac{,Nbe,Base}` | the same open term, but through tactic `norm_term` |

## Results

Measured with `./run.sh` (best of 5) on a 128-core shared machine.
Times are wall-clock milliseconds; `net` subtracts the `Bench.Empty` baseline.

```
module             norm_ms    nbe_ms  net_norm   net_nbe  speedup
Bench.Empty           2880      2949         -         -        -
Bench.Arith           4984      3726      2104       777     2.7x
Bench.List            5118      5038      2238      2089     1.1x
Bench.Sort            5217      5031      2337      2082     1.1x
Bench.Tree            3348      3216       468       267     1.8x
Bench.MachInt         7848      7776      4968      4827     1.0x
Bench.HO              4934      4976      2054      2027     1.0x
Bench.Share           4939      4958      2059      2009     1.0x
Bench.Dead            5215      5149      2335      2200     1.1x
Bench.Sym             5498      4553      2618      1604     1.6x

# tactic-level norm_term on an open term (baseline = Bench.SymTacBase)
Bench.SymTac         18880     18494       721       335     2.2x
```

### The effect of the normalizer memoization fix

These numbers were taken **after** merging the normalizer memoization fix for
[#4394](https://github.com/FStarLang/FStar/issues/4394)
([PR #4397](https://github.com/FStarLang/FStar/pull/4397)), which gives the
`cfg_memo` cache one slot per cfg so that the weak normalization of a match
scrutinee no longer evicts the strong normal forms of everything in the
environment. That fix removes a quadratic factor and closes most of the gap:

| module | net_norm before #4397 | net_norm after | net_nbe | speedup before | after |
|---|---|---|---|---|---|
| `Bench.Arith` | 8135 | 2104 | 777 | 14.1x | 2.7x |
| `Bench.List` | 7062 | 2238 | 2089 | 3.6x | 1.1x |
| `Bench.Sort` | 2354 | 2337 | 2082 | 1.2x | 1.1x |
| `Bench.Tree` | 393 | 468 | 267 | 3.2x | 1.8x |
| `Bench.MachInt` | 4636 | 4968 | 4827 | 1.0x | 1.0x |
| `Bench.HO` | 2894 | 2054 | 2027 | 1.5x | 1.0x |
| `Bench.Share` | 2270 | 2059 | 2009 | 1.2x | 1.0x |
| `Bench.Dead` | 1787 | 2335 | 2200 | 0.9x | 1.1x |

The `net_nbe` column is unchanged across the merge (PR #4397 touches only
`FStarC.TypeChecker.Normalize`), which is a useful control: it confirms the
before/after difference is the patch and not the machine.

### Reading the numbers

**NBE still wins on closed, computational reduction, but by much less than it
used to.** `Bench.Arith` remains the best case at 2.7x: pure first-order
arithmetic recursion with no residual term, where NBE compiles to native OCaml
closures and the normalizer pays for building, substituting into and
re-inspecting syntax at every step. `Bench.Tree` is 1.8x. Everything else —
lists, sorting, higher-order code, sharing, dead arguments — is now within
10% of the normalizer.

**NBE is neutral where primops dominate.** `Bench.MachInt` is 1.0x: both engines
call exactly the same `FStar.UInt32` primitive-step implementations, and the
interpretive overhead the two differ on is a small fraction of the total.

**NBE also wins on open terms**, by 1.6x for a norm request under a binder
(`Bench.Sym`) and 2.2x through tactic `norm_term` (`Bench.SymTac`). This
contradicts the intuition that readback should make NBE lose here: building a
20000-node residual term does cost NBE a readback pass, but the normalizer pays
more, because every one of those nodes is reached by substituting into and
re-inspecting syntax.

Note that the two symbolic benchmarks measure a small signal against a large
fixed cost, and `Bench.SymTac*` especially so — `open FStar.Tactics.V2` alone
costs about 18 s of module loading, against which the measured difference is
a few hundred milliseconds. An earlier version of this benchmark used a term
two orders of magnitude smaller and reported a 19x NBE *slowdown*; that was
pure noise. If you change these modules, check that the net column is at least
a few hundred ms and that repeated runs agree in sign.

**Memoization and laziness no longer favour the normalizer.** `Bench.Share`
(1.0x) and `Bench.Dead` (1.1x) were designed to be call-by-name's best cases —
a shared subcomputation and a discarded argument. Before #4397 the normalizer
won `Bench.Dead` by ~6%; it no longer wins either. NBE's constant-factor
advantage covers the work it wastes on the dead argument.

### Summary of the tradeoff

Since #4397, NBE buys roughly 2-3x on closed first-order computation, up to
about 2x on producing large residual terms, and essentially nothing (within
noise) on list, higher-order, sharing and primop-bound code. It is no longer a
loss anywhere in this suite. The remaining argument against making it the
default is correctness surface, not speed: the normalizer is the reference
semantics, NBE evaluates arguments call-by-value, drops `Tm_ascribed`, and
cannot reify layered effects (so `--__tactics_nbe` does not work).
