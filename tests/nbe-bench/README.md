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
Bench.Empty           2270      2287         -         -        -
Bench.Arith           3744      2767      1474       480     3.1x
Bench.List            3876      3828      1606      1541     1.0x
Bench.Sort            4017      3902      1747      1615     1.1x
Bench.Tree            2529      2461       259       174     1.5x
Bench.MachInt         5821      5786      3551      3499     1.0x
Bench.HO              3805      3802      1535      1515     1.0x
Bench.Share           3771      3790      1501      1503     1.0x
Bench.Dead            3761      3857      1491      1570     0.9x
Bench.Sym             4463      3641      2193      1354     1.6x

# tactic-level norm_term on an open term (baseline = Bench.SymTacBase)
Bench.SymTac         14454     14009       756       311     2.4x
```

### The effect of the normalizer memoization fix

These numbers were taken **after** merging the normalizer memoization fix for
[#4394](https://github.com/FStarLang/FStar/issues/4394)
([PR #4397](https://github.com/FStarLang/FStar/pull/4397)), which gives the
`cfg_memo` cache one slot per cfg so that the weak normalization of a match
scrutinee no longer evicts the strong normal forms of everything in the
environment. That fix removes a quadratic factor and closes most of the gap:

| module | net_norm before #4397 | net_nbe | speedup before | speedup after |
|---|---|---|---|---|
| `Bench.Arith` | 8135 | 579 | 14.1x | 3.1x |
| `Bench.List` | 7062 | 1959 | 3.6x | 1.0x |
| `Bench.Sort` | 2354 | 2046 | 1.2x | 1.1x |
| `Bench.Tree` | 393 | 121 | 3.2x | 1.5x |
| `Bench.MachInt` | 4636 | 4658 | 1.0x | 1.0x |
| `Bench.HO` | 2894 | 1914 | 1.5x | 1.0x |
| `Bench.Share` | 2270 | 1843 | 1.2x | 1.0x |
| `Bench.Dead` | 1787 | 1969 | 0.9x | 0.9x |

The `net_nbe` column is unchanged across the merge (PR #4397 touches only
`FStarC.TypeChecker.Normalize`), which is a useful control: it confirms the
before/after difference is the patch and not the machine.

#### The fix removes an asymptotic factor, not a constant

`Bench.Sym` builds a residual term of `n` applications, so it can be scaled to
show the shape of the bug directly. Best-of-3 wall clock, whole-file, in
seconds:

| n | before #4397 | after #4397 | speedup |
|---|---|---|---|
| 1000 | 5.91 | 0.30 | 20x |
| 2000 | 22.88 | 0.44 | 52x |
| 4000 | 91.21 | 0.68 | 134x |
| 8000 | 368.38 | 1.17 | 315x |
| 20000 | >26 min (abandoned) | 2.67 | >580x |

Before the fix each doubling of `n` costs **4x** the time — textbook quadratic.
After it, net of the ~0.15s process baseline (0.15 / 0.29 / 0.53 / 1.02), each
doubling costs **2x** — linear. So the speedups above are not a fixed factor;
they grow without bound with the size of the residual term, which is why the
same patch looks like 1.0x on `Bench.MachInt` and 315x here.

To reproduce, copy `Bench.Sym.fst`, change `upto 20000` to the size you want,
and time the two compilers on the same file.

#### The fix changes no observable output

PR #4397 is a caching change, so the interesting question is whether it
perturbs any result. Three checks, comparing a build at the merge base against
one at the merge:

- all **319** `ulib` `.checked` files are byte-identical;
- all **97** extracted `ulib` `.ml` files are byte-identical (and 313 of the
  320 compiler ones — the 7 that differ are exactly the files edited on this
  branch);
- the `--log_queries` SMT output for the 8 closed benchmarks above is
  byte-identical apart from the F* commit hash written into a comment.

### Reading the numbers

**NBE still wins on closed, computational reduction, but by much less than it
used to.** `Bench.Arith` remains the best case at 3.1x: pure first-order
arithmetic recursion with no residual term, where NBE compiles to native OCaml
closures and the normalizer pays for building, substituting into and
re-inspecting syntax at every step. `Bench.Tree` is 1.5x. Everything else —
lists, sorting, higher-order code, sharing, dead arguments — is now within
10% of the normalizer.

**NBE is neutral where primops dominate.** `Bench.MachInt` is 1.0x: both engines
call exactly the same `FStar.UInt32` primitive-step implementations, and the
interpretive overhead the two differ on is a small fraction of the total.

**NBE also wins on open terms**, by 1.6x for a norm request under a binder
(`Bench.Sym`) and 2.4x through tactic `norm_term` (`Bench.SymTac`). This
contradicts the intuition that readback should make NBE lose here: building a
20000-node residual term does cost NBE a readback pass, but the normalizer pays
more, because every one of those nodes is reached by substituting into and
re-inspecting syntax.

Note that the two symbolic benchmarks measure a small signal against a large
fixed cost, and `Bench.SymTac*` especially so — `open FStar.Tactics.V2` alone
costs about 14 s of module loading, against which the measured difference is
a few hundred milliseconds. An earlier version of this benchmark used a term
two orders of magnitude smaller and reported a 19x NBE *slowdown*; that was
pure noise. If you change these modules, check that the net column is at least
a few hundred ms and that repeated runs agree in sign.

**Memoization and laziness barely favour the normalizer.** `Bench.Share` (1.0x)
and `Bench.Dead` (0.9x) were designed to be call-by-name's best cases — a shared
subcomputation and a discarded argument. `Bench.Dead` is the only kernel where
the normalizer wins, and only by ~5%, at the edge of the noise floor: NBE's
constant-factor advantage very nearly covers the work it wastes evaluating an
argument that is then thrown away. The normalizer's memoization recovers most of
the sharing NBE gets for free from call-by-value.

### Summary of the tradeoff

Since #4397, NBE buys roughly 2-3x on closed first-order computation, up to
about 2x on producing large residual terms, and essentially nothing (within
noise) on list, higher-order, sharing and primop-bound code. Its only loss in
this suite is ~5% on a discarded argument. The remaining argument against
making it the default is correctness surface, not speed: the normalizer is the reference
semantics, NBE evaluates arguments call-by-value, drops `Tm_ascribed`, and
cannot reify layered effects (so `--__tactics_nbe` does not work).
