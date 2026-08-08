# The two reduction engines

F* ships two normalizers:

* **`FStarC.TypeChecker.Normalize`** — call-by-name with memoization. This is the
  **reference** behaviour. Any observable disagreement between the two engines is
  by definition an NBE bug.
* **`FStarC.TypeChecker.NBE`** — normalization by evaluation, call-by-value.
  Usually faster, most markedly on closed first-order computation.

This document records where each engine is used, how to switch between them, and
which differences are known and deliberately tolerated.

## How the dispatch works

Every reduction in the compiler goes through
`Normalize.normalize_with_primitive_steps ps s e t`, which branches on
`is_nbe_request s`, i.e. on whether `Env.NBE` appears in the requested steps:

```
normalize_with_primitive_steps ps s e t
  | is_nbe_request s -> nbe_eval c s t   (* -> (cfg_env cfg).nbe, installed in FStarC.Universal.init_env *)
  | otherwise        -> norm c [] [] t   (* the call-by-name normalizer *)
```

So the only question is who puts `Env.NBE` into the step list. There are exactly
four ways, listed below.

### 1. `--use_nbe true`

`Cfg.add_nbe` sets `nbe_step` in *every* cfg, and
`Normalize.handle_norm_request` turns that into an `NBE` step for every
**explicit norm request** it encounters while normalizing:

* `assert_norm`
* `normalize_term` / `normalize`
* `norm [..]` and `norm_spec`
* library preconditions that are themselves norm requests, most importantly
  `FStar.Calc.calc_finish`'s
  `norm [delta_only [`%calc_chain_compatible; `%calc_chain_related]; iota; zeta] ...`
  — which is why a bug in this path breaks *every* `calc` proof in the codebase.

Note the asymmetry: `normalize_with_primitive_steps` tests the **raw** step list,
not the `add_nbe`-adjusted one. A direct call to `Normalize.normalize` therefore
ignores `--use_nbe` entirely. In particular **tactic-level `norm_term` is not
affected by `--use_nbe`**; see (4).

### 2. `--use_nbe_for_extraction true`

Selects NBE for extraction-time normalization in `FStarC.Extraction.ML.Term` and
`FStarC.Extraction.ML.Modul`.

### 3. `--__tactics_nbe`

Selects NBE for tactic execution (`FStarC.Tactics.Interpreter`, `Options.tactics_nbe`).

**This flag is still unusable**, but for one reason rather than two.

*Blocker 1 (fixed).* A tactic registered as a native plugin had
`interpretation_nbe = dummy_interp`, an unconditional `failwith` ("No
interpretation for `FStar.Tactics.Typeclasses.mk_class`"). It now gets a real
NBE interpretation, built by reading the arguments back into syntax, running the
syntactic interpretation, and translating the result — which is why `nbe_cbs`
carries a `readback` callback next to `iapp` and `translate`. That was reachable
from *any* NBE reduction meeting such a primitive, not just from this flag.

*Blocker 2 (not fixed; now explicit).* `TAC` is a **layered** effect, and NBE's
`translate_monadic` / `translate_monadic_lift` implement only the plain-effect
protocol. They used to build a malformed application and report it as `NBE
ill-typed application: Unknown`; they now fail up front naming the effect. A
real port has to mirror, from `Normalize`:

- the layered `bind_inst_args` argument convention — `bind a b <one unit per
  index binder> <2 ranges if the decl has `bind_has_range_args`> f g`, rather
  than `bind a b wp_f f wp_g g`;
- real universes from `env.universe_of` (NBE currently passes `U_unknown`, and
  readback of a universe variable is a `failwith`);
- `reify_lift`'s layered case, which deliberately uses the *lift* rather than
  the target's `return`, because that is what verification used;
- `Div`-let reduction under `steps.tactics`.

Until then, tactics run on the call-by-name normalizer; a tactic that wants NBE
can ask for it per-request with the `nbe` step, see (4).

### 4. The `nbe` norm step in source

`norm [nbe; delta; iota; zeta] e` opts a single request in. This is the *only*
way to select NBE for a tactic-level `norm_term`, since that path calls
`Normalize.normalize` directly and never reaches `handle_norm_request`.

## Everything else

Roughly 190 other call sites reduce terms — `N.normalize`, `N.unfold_whnf`,
`N.normalize_refinement`, `N.non_info_norm`, `N.remove_uvar_solutions`,
`N.get_n_binders`, and friends — distributed approximately as:

| file | sites |
|---|---|
| `FStarC.TypeChecker.TcTerm.fst` | 32 |
| `FStarC.TypeChecker.Util.fst` | 27 |
| `FStarC.TypeChecker.Rel.fst` | 25 |
| `FStarC.TypeChecker.TcEffect.fst` | 18 |
| `FStarC.TypeChecker.Tc.fst` | 14 |
| `FStarC.TypeChecker.Core.fst` | 11 |
| `FStarC.Tactics.V2.Basic.fst` | 10 |
| `FStarC.TypeChecker.TcInductive.fst` | 7 |
| `FStarC.TypeChecker.Generalize.fst` | 7 |
| `FStarC.Extraction.ML.Modul.fst` | 7 |
| `FStarC.Extraction.ML.Term.fst` | 5 |
| `FStarC.SMTEncoding.Encode.fst` | 4 |
| others (`Hooks`, `CtrlRewrite`, `EncodeTerm`, `Quals`, `Ide`, `RegEmb`, …) | ~23 |

**None of these is individually switchable**: not one passes `Env.NBE`, so they
always use the call-by-name normalizer. NBE can only be reached from them
indirectly, when the term being reduced itself contains a norm request — which
is exactly case (1). There is no per-site engine choice to make.

## Known differences

Two differences are deliberate and will not be fixed.

**Ascriptions.** `NBETerm.t` has no `Ascribed` node, so `translate` drops
`Tm_ascribed` (`NBE.fst`, `| Tm_ascribed {tm=t} -> translate cfg bs t`). Where
the normalizer prints `e <: prop`, NBE prints `e`. Adding an ascription node
would have to be threaded through `translate`, `readback`, `eq`, `to_string` and
`iapp`, and would break every primop and unembedding that matches on argument
shapes, for no soundness benefit: ascriptions are erasable and do not affect the
SMT encoding. Differential tests should include the `unascribe` step.

**Call-by-value argument evaluation.** NBE evaluates an argument before
substituting it, so a value can appear more reduced than call-by-name would ever
make it — e.g. a function passed as an argument can show up as a `fun` literal in
a position the normalizer would leave as an `fv`. Removing this means abandoning
CBV, i.e. abandoning NBE.

**Source ranges.** Readback attaches the ranges NBE recorded while building the
semantic value, which are not always the ones the normalizer would have carried
through. The difference is invisible in a normal form but shows up in the
location an error is reported at, and occasionally in whether a "See also"
secondary location is emitted at all.

Because of the last two, `tests/error-messages` does **not** diff clean under
`--use_nbe true`, and is not expected to: its golden files record ranges and
printed ascriptions, not just normal forms. As of this writing `AssertNorm`,
`Bug1997`, `Calc` and `QuickTest` differ, all three ways — dropped `<: prop`
ascriptions, differently numbered unification variables, and shifted ranges. The
VC bodies themselves are identical. Everything else in `tests/` diffs clean
under the flag.

## Writing a differential test

Regression tests for engine agreement live in
`tests/micro-benchmarks/Test.NBE.fst` and follow this shape:

```fstar
let test_X () =
  assert True by (
    let open FStar.Tactics.V2 in
    let steps = [delta_only [`%f]; iota; zeta; unascribe] in
    let t = `(f 3) in
    let a = norm_term steps t in
    let b = norm_term (nbe::steps) t in
    if term_to_string a = term_to_string b then () else
    fail ("NBE and the normalizer disagree: " ^ term_to_string a
          ^ " vs " ^ term_to_string b))
```

Three things to watch for:

* Always include `unascribe`, or every test trips over the ascription
  difference above.
* Avoid terms whose normal form contains unification variables. The two
  `norm_term` calls re-typecheck independently and produce
  differently-numbered uvars, so the comparison fails spuriously.
* When asserting "did this unfold?", match **both** `Tv_FVar fv` and
  `Tv_UInst fv _`. A universe-polymorphic head reads back as the latter, and a
  test that only matches `Tv_FVar` can pass for the wrong reason.
* A divergence can show up as a **hang**, not an error. When flipping a suite to
  `--use_nbe true`, run it under a timeout and check that it actually finished;
  a `make -k` that is still running is not a pass. Remember that
  `tests/bug-reports` has a `closed/` subdirectory, which is where the local
  let rec divergence above was hiding.
* Residual terms containing a local `let rec` cannot be compared with
  `term_to_string`: the two engines differ there in the two accepted ways above
  (NBE drops the body's ascription, and the printer renders the binder
  differently). Test termination and the resulting proof obligation instead.

## Termination

The reference normalizer stays terminating **not** by refusing to unfold
recursive definitions applied to symbolic arguments, but by clearing all
unfolding directives when it descends into the branches of an irreducible match
(`Normalize.cfg_exclude_zeta`). NBE originally had this backwards: a strong
`isAccu` guard on recursion, but a branch cfg that only turned `zeta` off. It now
mirrors the normalizer (`NBE.stuck_match_cfg`). The two halves must stay in sync
— relaxing the recursion guard without the stronger branch cfg diverges.

The stopping half has to cover **both** recursion paths in `NBE.iapp`:

* `TopLevelRec` stops because `still_unfoldable` rejects the fv once
  `stuck_match_cfg` has stripped the delta levels.
* `LocalLetRec` has no fv and therefore no delta level, so the only thing that
  can stop it is `zeta`, which it must test explicitly — exactly as the
  normalizer's `Tm_let` case does with `not cfg.steps.zeta && not
  cfg.steps.zeta_full`.

Missing the second one is not caught by any closed-term test: it needs a local
`let rec` scrutinising a *symbolic* argument, as in
`tests/bug-reports/closed/Bug1622.fst`.

## Benchmarks

`tests/nbe-bench/` measures the tradeoff; see its `README.md`. In short, since
the normalizer memoization fix in
[PR #4397](https://github.com/FStarLang/FStar/pull/4397), NBE is worth about
2-3x on closed first-order computation, about 2x on producing large residual
terms from open ones, and nothing measurable on list, higher-order, sharing and
primop-bound code. It is not a loss anywhere in that suite. The argument against
making it the default is therefore correctness surface, not speed: see *Accepted
differences* above.

Beware when benchmarking open/symbolic terms: `open FStar.Tactics.V2` alone
costs about 14 s of module loading, so a small kernel measures nothing but
noise. An earlier version of `Bench.Sym` did exactly that and reported a
spurious 19x NBE slowdown.

## Testing a change to either engine

A change to `NBE.fst` or `Normalize.fst` should be validated with a full clean
bootstrap and the Pulse suites, since Pulse is by far the heaviest user of both
engines:

```
make clean
make -j$(nproc) stage3          # stage3 = stage2 + Pulse
make -j$(nproc) test-3          # all F* tests + pulse/test + pulse examples
OTHERFLAGS="--use_nbe true" make -j$(nproc) _test_pulse
```

**Pass `OTHERFLAGS` through the environment, not as a `make` argument.** The
Pulse makefiles build their flags up with `OTHERFLAGS += ...` — for instance
`pulse/test/pool/pulse_task/Makefile` adds
`--include $(PULSE_ROOT)/share/pulse/examples`, and `pulse/mk/test.mk` adds
`--ext optimize_let_vc` and `--ext fly_deps`. A variable set on the make command
line cannot be appended to by the makefile, so `make OTHERFLAGS=...` silently
drops all of those and the run fails with an unrelated-looking
`Error 134: Namespace 'Quicksort.Base' cannot be found`. Setting the variable in
the environment lets the `+=` work as intended.
