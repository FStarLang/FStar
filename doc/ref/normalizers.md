# The two reduction engines

F* ships two normalizers:

* **`FStarC.TypeChecker.Normalize`** — call-by-name with memoization. This is the
  **reference** behaviour. Any observable disagreement between the two engines is
  by definition an NBE bug.
* **`FStarC.TypeChecker.NBE`** — normalization by evaluation, call-by-value.
  Usually faster on closed computation, slower on open terms.

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

**This flag is currently broken.** `TAC` is a layered effect and NBE cannot reify
it, so essentially any tactic fails with an assertion. It should not be used.

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

## Termination

The reference normalizer stays terminating **not** by refusing to unfold
recursive definitions applied to symbolic arguments, but by clearing all
unfolding directives when it descends into the branches of an irreducible match
(`Normalize.cfg_exclude_zeta`). NBE originally had this backwards: a strong
`isAccu` guard on recursion, but a branch cfg that only turned `zeta` off. It now
mirrors the normalizer (`NBE.stuck_match_cfg`). The two halves must stay in sync
— relaxing the recursion guard without the stronger branch cfg diverges.

## Benchmarks

`tests/nbe-bench/` measures the tradeoff; see its `README.md`. In short, NBE is
worth 3-13x on closed first-order computation, neutral where primops dominate,
and roughly an order of magnitude *slower* on open terms — the regime tactics
operate in.
