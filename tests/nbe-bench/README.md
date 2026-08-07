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
startup and `Prims`/`FStar` loading, ~2.3 s) to get the `net` column. The
minimum is the only meaningful statistic on a shared machine.

## Selecting the engine

`--use_nbe true` sets `nbe_step` in the ambient cfg
(`Cfg.add_nbe`), which `Normalize.handle_norm_request` turns into an `NBE` step
for every *explicit* norm request encountered while normalizing — `assert_norm`,
`normalize_term`, `norm [..]`, `norm_spec`, and library preconditions such as
`FStar.Calc.calc_finish`'s. That is what `Bench.Arith` … `Bench.Dead` exercise.

It does **not** affect tactic-level `norm_term`, which calls
`Normalize.normalize` directly and so never passes through
`handle_norm_request`. To benchmark that path the engine has to be selected with
the explicit `nbe` norm step, which is why `Bench.Sym` (normalizer),
`Bench.SymNbe` (NBE) and `Bench.SymBase` (no normalization) are three separate
modules rather than one module under two flags.

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
| `Bench.Sym`, `Bench.SymNbe`, `Bench.SymBase` | `norm_term` on an *open* term whose result stays a large residual term |

## Results

Measured with `./run.sh` (best of 5) on a 128-core shared machine at load ~47.
Times are wall-clock milliseconds; `net` subtracts the `Bench.Empty` baseline.

```
module             norm_ms    nbe_ms  net_norm   net_nbe  speedup
Bench.Empty           2348      2348         -         -        -
Bench.Arith           8431      2831      6083       483    12.6x
Bench.List            8107      3948      5759      1600     3.6x
Bench.Sort            4330      4004      1982      1656     1.2x
Bench.Tree            2701      2511       353       163     2.2x
Bench.MachInt         5996      5911      3648      3563     1.0x
Bench.HO              4762      3901      2414      1553     1.6x
Bench.Share           4231      3876      1883      1528     1.2x
Bench.Dead            3858      3949      1510      1601     0.9x

# tactic-level norm_term on an open term (baseline = Bench.SymBase)
Bench.Sym            14127     15135        56      1064     0.1x
```

### Reading the numbers

**NBE wins on closed, computational reduction.** `Bench.Arith` is the best case
at ~13x: pure first-order arithmetic recursion with no residual term, where NBE
compiles to native OCaml closures and the normalizer pays for building,
substituting into and re-inspecting syntax at every step. `Bench.List` (3.6x)
and `Bench.Tree` (2.2x) are the same story with data structures.

**NBE is neutral where primops dominate.** `Bench.MachInt` is 1.0x: both engines
call exactly the same `FStar.UInt32` primitive-step implementations, and the
interpretive overhead the two differ on is a small fraction of the total.

**NBE loses on open terms** — `Bench.Sym` is 0.1x, i.e. NBE is roughly 19x
slower. Once the result is a large residual term, NBE has to pay for readback:
every accumulator has to be turned back into syntax, and every argument that
call-by-name would have left untouched has already been evaluated into a
closure. This is the single clearest argument against making NBE the default:
it is exactly the regime tactics operate in.

**Memoization and laziness matter less than expected.** `Bench.Share` (1.2x) and
`Bench.Dead` (0.9x) were designed to be call-by-name's best cases — a shared
subcomputation and a discarded argument. `Bench.Dead` is the only kernel where
the normalizer wins outright, and only by ~6%, which is close to the noise
floor. The normalizer's memoization recovers most of the sharing NBE gets for
free from call-by-value, and NBE's constant-factor advantage nearly cancels the
work it wastes on the dead argument.

### Summary of the tradeoff

NBE is worth 3-13x on closed computation, is free on primop-bound code, and is a
large loss on open terms. `--use_nbe true` is therefore a good choice for proofs
dominated by `assert_norm` over concrete data, and a bad default for tactic-heavy
developments.
