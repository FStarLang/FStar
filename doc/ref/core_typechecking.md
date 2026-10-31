# Typechecking with Core

*A reference for F\* compiler developers.*

`FStarC.TypeChecker.Core` is the only generator of verification conditions
in F\*. Every term of a top-level declaration is checked in two steps:

1. **Elaboration.** `TcTerm` runs once, with `admit = true`. It infers
   implicit arguments, universes and types, inserts coercions, and runs
   tactics. It proves nothing: the guards it builds are discarded. The
   result is a fully elaborated term with no unification variables.
2. **Checking.** Core checks the elaborated term as it is, and computes its
   verification condition (VC), which is sent to the SMT solver.

Core is a checker, not an elaborator. It does no unification and no
inference of implicits. It is self-contained, which makes it a small,
auditable basis for a more trustworthy core of F\*.

The unifier, `Rel`, is part of elaboration. It solves unification variables
but computes no logical guard (§3).

The design builds on the simplified effect system (see
[simplified_effect_system.md](simplified_effect_system.md)). Because `Tot`,
`GTot` and `Div` are primitive, and specifications live in refinements
rather than in WPs, Core only knows three kinds of computation: `ETot`,
`EGhost`, and an opaque *effectful* `EEff m`.

In lax mode (a lax module, `--admit_smt_queries true`, or while
elaborating), `env.admit` is set and Core does not run: terms are only
elaborated (`CoreCheck.enabled`, `CoreCheck.check_or_elaborate`).

Contents:

1. [The driver](#1-the-driver)
2. [Declarations other than `let`](#2-declarations-other-than-let)
3. [Rel as an elaborator](#3-rel-as-an-elaborator)
4. [What Core had to learn](#4-what-core-had-to-learn)
5. [Guards and facts](#5-guards-and-facts)
6. [What `.checked` files record](#6-what-checked-files-record)
7. [Known limitations](#7-known-limitations)
8. [Debugging](#8-debugging)
9. [Performance](#9-performance)

---

## 1. The driver

The driver for `let` is `Tc.tc_sig_let`, together with
`Tc.tc_sig_let_core`.

* **Elaboration.** `elaborate ()` runs `TcTerm` with `admit` set, inside
  `Tc.elaborating`, which clears Core's memo table (the elaboration's
  guards are not proven, so nothing it caches may be trusted). In a lax
  module the driver stops there, after `CoreCheck.check_smt_patterns`
  (§2).
* **Non-recursive `let`.** The elaborated definition is checked with
  `Core.compute_term_comp` against an expected type:
  * the user's annotation, if there is one;
  * otherwise, **the type elaboration inferred** (`elab_lbtyp`, remembered
    by `drop_lbtyp`).

  Core does no inference, even at the top level. Clients depend on the
  recorded type (§6). With `--ext core_infer`, Core infers the type
  instead. The inferred computation type is then normalized with `Beta;
  Eager_unfolding; NoFullNorm; Exclude Zeta`. Only the result of the arrow
  is normalized; its binders are left as written.

  A declared type is checked for well-formedness on its own first
  (`check_declared_types`), and its guard is discharged as a separate query.
  Core caches what it proves, so checking the definition does not emit that
  guard again. In one guard, the type's conjunct, quantified over the
  binders of the type, would be a hypothesis of every goal of the
  definition (see §5 on `split_goals`). That derails the SMT solver, e.g.
  with nonlinear terms like `pow2 (hi - lo)` in the precondition. This
  applies to the user's annotation, to the declared types of a nest of
  recursive definitions, and to the elaborated type of a definition whose
  result is annotated, as in `let f x : Lemma (requires p x) (ensures q x)
  = e` (`result_annotated`).

  An inferred type is not checked (`check_t = false`). It may only be
  well-formed in the context the definition sets up. For example, for
  `let n = f b in lem b; U32.uint_to_t n` the type is `x:U32.t{v x = f b}`,
  where `=` is taken at `uint_t 32`.

  The definition is then finished by `TcTerm.finish_top_level_let`. It
  masks top-level effects, checks that the type is inhabited, applies
  tcnorm, and closes the universes. Core's guard is discharged there, with
  the user's annotation, not the inferred type, as `topt`.
* **Recursive `let`s.** These use `Core.check_top_level_letrec`. The
  recursive names are replaced by fresh variables. Their types are refined
  for termination using `Termination.guard_letrecs`, and the nest is checked like
  an inner `let rec`.
* **Failures.** Only Core decides whether a definition is accepted, and
  Core reports why it is not.
  * An unprovable guard is reported by the SMT solver, with the labels and
    ranges Core puts on the guard (§7, "Error reporting").
  * A structural failure is reported with Core's error. Where TcTerm has an
    error code for the same failure, Core's error carries it
    (`Core.error_code`) and is reported with it and with TcTerm's message:
    Error 34 for a computation of the wrong effect (e.g. `GTot` for `Tot`),
    Error 236 for a `when` clause. Any other structural failure is Error 12,
    "Core failed to check this definition", followed by Core's context. It
    is located at the innermost term of that context (`Core.error_range`).

### Ill-scoped elaborations

Core checks the elaboration as it is, so the elaboration must be closed.
A definition whose elaboration has free names is rejected with an internal
error (Error 327, `Error_IllScopedTerm`).

Four bugs in TcTerm and Rel used to leave free names in the elaboration.
All four broke the invariant `Rel` relies on: every occurrence of a uvar is
in the scope of its whole context, except for the names its delayed
substitution maps. `Rel.ensure_no_uvar_subst` may solve a uvar `?u` as
`?v x1 .. xn`, over the suffix of its context that a substitution affects.
An occurrence of `?u` outside the scope of some `xi` then has `xi` free.

* *The scrutinee in a branch's environment.* `TcTerm.tc_eqn` checked a
  branch in an environment containing the match's logical scrutinee
  `guard_x`, which is never bound in the term when the scrutinee is pure.
  A uvar created in the branch could be solved as `?v ... guard_x ...`
  (e.g. the typeclass dictionaries in `fun (a,b) (c,d) -> eq a c && eq b d`,
  `examples/typeclasses/Eq.eq_pair`). The branch is now checked without
  the scrutinee. The pattern's guard and the branch's equations add it to
  their own environments (`scrutinee_env`).
* *Eta-contraction in `Rel.mk_solution`.* `?m x =?= h e x` is solved with
  `?m := h e` when `x` is not free in `h e`. That check missed a uvar `?d`
  in `e` whose context contains `x`: `restrict_all_uvars` then solved
  `?d := ?d' x`, out of scope (`tests/custard/Mymon`). Now the uvars of the
  contracted solution are restricted to the binders it still abstracts
  over. The contraction is refused if `x` occurs in the type of such a uvar.
* *A type escaping a binder.* The result type of `let x = e1 in e2`, or of
  a branch, is used outside the scope of `x`, or of the pattern's
  variables, and may contain a uvar whose context includes them (e.g.
  `PulseCore.Action.lift_pre_act0_act`). `Rel.restrict_escaping_uvars` now
  restricts every such uvar to its context minus the escaping names (and
  the binders whose sorts depend on them). It is called by
  `TcUtil.composite_result_typ` for a `let`, and by `TcTerm.tc_eqn` for a
  branch. A uvar whose type mentions an escaping name is left alone.
* *An ill-scoped uvar type in `Rel.restrict_ctx`.* To solve `?m y =?= e`,
  each uvar `?s` of `e` is restricted to the part of its context shared
  with `?m`'s, plus `y`. The restriction ignored the delayed substitution
  of `?s`'s occurrence, and `?s`'s type could mention a dropped name
  (`Pulse.C.Types.Scalar.read_prf`). Now the new uvar is also abstracted
  over the dropped binders its type depends on.

### Elaboration must be complete

Nothing re-elaborates the elaborated term. It is what Core checks, and also
what is recorded, extracted and reified. So it must carry everything a
checked term carries:

* **Types of inner `let`s.** `TcTerm.check_inner_let` records the inferred
  type of every unannotated inner `let`, since Core needs a type on every
  binder. That type must therefore be right. `Rel` used to solve a flex
  variable from lower bounds with different base types by joining them,
  equating the bases (typically false). Now the lower bounds are joined
  only if they share a base type (`lower_bounds_share_a_base`; everparse's
  `CDDL.Spec.AST.Elab.Included.Array`,
  `tests/bug-reports/closed/Phase2CoreJoinBases`).
* **Monadic annotations.** `Meta_monadic`, `Meta_monadic_lift` and `lbeff`
  must follow the rule of `check_inner_let`: the definition is lifted to the
  effect of the whole `let`, which is also its `lbeff`. Three
  let-insertions in TcTerm were fixed to follow it:
  * `tc_match`, for an impure scrutinee: `let x = e in match x with ...`
    lifts `e` to the effect of the match, and uses that effect as `lbeff`.
    Otherwise a `Dv` scrutinee in `Tac` code is extracted as reified `TAC`.
  * `tc_app`, when binding effectful arguments (`bind_lifted_args`): `lbeff`
    and `Meta_monadic` use the effect of the application, not of the
    argument. Otherwise reifying the application fails.
  * `maybe_elaborate_short_circuit_args`: `e1 && e2` / `e1 || e2` with an
    effectful operand is rewritten to `if` (preceded by a `let` when `e1` is
    effectful). The rewritten term is checked again with `tc_term`, which
    inserts the annotations (`tests/custard/plugin`,
    `CustardPlugin.sc_left`, `sc_right`).
* **Tactics that produce terms.** `synth_by_tactic` at a type that is not
  a proposition runs during elaboration, and its result is left in the
  elaborated term (see "Tactic synthesis" below for the other case). A goal
  may mention uvars that are solved only after the tactic would run: in
  `f h (_ by tac)`, the implicits of `f` may wait on the deferred subtyping
  of `h`. So a definition that mentions `synth_by_tactic` is elaborated
  twice: first without synthesis, then with it (`TcUtil.with_synth`), over
  the first elaboration, whose goals are fully resolved. Other callers of
  TcTerm do not run synthesis (`TcUtil.synth_mode`): see the known gap
  below.
* **Projector types of parameterized inductives** (`TcInductive`). A
  projector's type substitutes the earlier fields of the constructor by
  projections of the projectee. These projections take the type's
  parameters as implicit arguments; they used to be built without them,
  which Rel tolerated but Core rejects.

### Tactic synthesis

With two phases, phase 1 left `synth_by_tactic tau` in place, and phase 2
ran the tactic and used its result at the requested type: the VC generator
was the one that ran the tactic, so nothing checked the result afterwards.
Now Core checks every elaborated term from scratch, and nothing a tactic
produces is trusted. There are two cases, decided by
`VCUtil.synth_proof_goal`, which TcTerm and Core share:

* **Proofs.** When the requested type is a proof goal, i.e. all of its
  inhabitants are `()` (`squash p`, `u:unit{p}`, or a proposition such as
  `a == b`), the elaborator does not run the tactic
  (`TcTerm.tc_synth`): it leaves `synth_by_tactic #t tau` in the term.
  Core checks it as an application and adds the guard `with_tactic tau p`,
  as for `assert p by tau`: the tactic proves the goal that Core computes,
  in Core's context, when the guard is discharged. Re-checking a result
  `()` against `squash p` instead would ask the SMT solver to prove what
  the tactic proved, which may be well beyond it (nonlinear arithmetic in
  `FStar.UInt128`, `FStar.Math.Euclid`). Once Core has accepted the
  definition, the driver replaces these applications by `()`
  (`Tc.erase_synthesized_proofs`) before recording it. In a lax
  definition, Core does not run, nor do these tactics.
* **Other terms.** The elaborator runs the tactic, and Core checks its
  result like any other term. The result is left as the tactic wrote it,
  without an ascription, so that clients and tactics (e.g. `def_of` in
  `examples/tactics/Normalization.fst`) see it as written. Core rejects a
  `synth_by_tactic` left unrun at such a type: the library's declaration
  of `synth_by_tactic` (`Tot t`) would otherwise give a value of any type
  with no obligation.

For `e <: t by tac`, Core wraps the guard of the ascription with the tactic
(`with_ascription_tactic`), even when the guard is trivial. The tactic is
checked to be a total `unit -> Tac unit` (`check_ascription_tactic`), as by
`TcTerm.tc_tactic`.

**Known gap: synthesis outside `let`.** Only the definitions of top-level
`let`s are elaborated with synthesis (`Tc.tc_sig_let`). A
`synth_by_tactic` at a type that is not a proposition elsewhere, e.g. in
the type of a `val` or `assume val`, or of a constructor's argument, is not
run, and Core rejects it ("This synthesis by a tactic was not run").
Before Core, phase 2 ran these. To be revisited.

### Guards are simplified before discharge

The driver simplifies Core's guard (`Rel.simplify_guard`) before
discharging it (`CoreCheck.discharge`). It matters for normalization
requests: in `norm [nbe; primops] ("a" ^ "b") == "ab"`, the simplifier
reduces the argument's primitive application first, whereas processing the
request itself, with only `primops`, does not unfold `(^)`.

Core also simplifies (`VCUtil.simplify_vc`) the guard of a refinement of
`unit` it witnesses, e.g. `()` against `squash p`. This head-unfolds
`unfold` abbreviations, e.g. `normal p` into the `norm [...] p` request it
stands for, and a tactic that processes the VC may depend on it
(`OPLSS2021.ValeVCNoProp`).

The driver opens the leading quantifiers of a top-level guard, e.g. over
the binders of `let f x y = ...`, into the environment in which it
discharges the guard (`open_foralls`). A `handle_smt_goals` tactic then
sees `False` rather than `forall (_:unit). False`
(`examples/tactics/HandleSmtGoal`). For a `let rec`, the names of the nest
are bound before the binders (see §5).

## 2. Declarations other than `let`

Core checks every term of a declaration whose checking matters for
soundness. Each term is elaborated with `admit` set, and Core checks the
elaboration. The common part lives in `FStarC.TypeChecker.CoreCheck`:

* `enabled env` holds when `env.admit` is not set.
* `check_or_elaborate env core elab` runs `core ()` when Core is enabled,
  and `elab ()` otherwise.
* `elaborate env tc e` runs `tc` with `admit` set, solves the implicits,
  removes the uvar solutions, and clears Core's memo table before and
  after.
* `check_term`, `compute_term_type`, `universe_of`, `check_binders` and
  `check_subtyping` call Core and `discharge` its guard. A structural
  failure is reported with Core's error code and message, if it has one
  (`raise_core_error`).

| declaration, or part of it | how it is checked |
|---|---|
| `val` (`Sig_declare_typ`) | Core checks that the elaborated type scheme is a type (`Tc.check_type_scheme_with_core`). |
| `assume` (`Sig_assume`) | The same, but the formula must have type `prop`. In this Prims `prop` is an `assume val`, not `Type`, so `universe_of` would reject it. |
| inductives (`Sig_bundle`, `TcInductive`) | The bundle is elaborated with `admit`; then `TcInductive` runs again on the elaboration, and checks its terms with Core: the parameters, indices and kind of each type (`check_or_elab_binders`, `check_or_elab_type`), the arguments and result type of each constructor (`check_or_elab_tparams`), the binders of the injectivity-on-parameters check, and the hasEq formula against `prop`. A `val` that predeclares an inductive must agree with it (`Core.check_term_equality`). |
| projectors, discriminators, hasEq axioms | Generated as `val`s, `let`s and `assume`s, and checked through those paths. |
| effects (`TcEffect`) | Every combinator is elaborated, then checked by Core against its expected type (`check_comb`). Core also computes the universe of a representation (`repr_universe`). |
| `sub_effect` | The lift is elaborated (`tc_lift` with `admit`, then `elim_uvars`) before it is checked, so that the terms Core checks are closed. |
| attributes | Elaborated, then Core computes their types (`Tc.tc_decl_attributes`). |
| implementation vs. interface `val` | `check_subsumes_iface_val` asks Core whether the implementation's type is a subtype of the interface's (`CoreCheck.check_subtyping`). |
| `[@@no_subtyping]` | Core checks the type with `use_eq_strict` set. In that mode, `Core.check_relation` checks `EQUALITY` where it would check `SUBTYPING`. Core accepts lemmas (`int : eqtype` vs `Type`) and rejects actual subtyping, e.g. `nat` for `int` (`tests/bug-reports/closed/Phase2CoreNoSubtyping`). |
| `%splice` tactics (`Hooks.splice`) | The tactic is elaborated; Core checks it against `dsl_tac_t` (typed splices) or `unit -> Tac decls`. |
| tactics run by the interpreter (`Interpreter.run_tactic_on_ps`) | When the tactic is not already typed, e.g. in `assert ... by`, `synth_by_tactic` or `postprocess_with`, it is elaborated (`TcTerm.tc_tactic`), and Core checks it against `a -> Tac b`. |
| `#check` | The term is elaborated, and Core checks it at the inferred computation type (`Core.check_term_at_comp`). Core's guard is shown, not discharged. |
| `#eval` | Core computes the computation type of the elaboration (`Core.compute_term_comp`). The guard is not discharged. |
| `__tc`, `__tc_ghost` (`V2.Basic.tc_with_core`) | TcTerm elaborates with `admit`; Core computes the type and the guard, which becomes a goal. |

**SMT-pattern warnings.** Core reports no Warning 271 (a pattern that misses
a bound variable, or uses theory symbols). `CoreCheck.check_smt_patterns`
walks the arrows of what was checked (`val`/`assume` types, `let` bodies,
constructor arguments) and calls `TcTerm.check_smt_pat` on them, in lax
mode too. The uvars in the patterns of lemma types must be removed, so
`Normalize.norm_comp` processes the `SMTPAT` flag when `compress_uvars` is
set (`tests/bug-reports/closed/Phase2CoreLemmaPatterns.fst`).

**Binder names.** Core names the binders it opens deterministically, so
that its checks can be memoized. Its indices start at 2^40
(`Core.core_index_base`), so that they never collide with the names
`GenSym` produces, e.g. for the local binders of a constructor's arguments
(`tests/bug-reports/closed/Phase2CoreBinderNames.fst`).

**Terms not checked again.** These are justified otherwise:

* The result of postprocessing (`postprocess_with`,
  `postprocess_for_extraction_with`) is justified by the equality proof the
  tactic must produce.
* Typed splices that claim their result is already checked
  (`checked = true`, e.g. Pulse) are trusted. This rests on the type of
  the splice tactic, `dsl_tac_t`, which Core checks.

## 3. Rel as an elaborator

`FStarC.TypeChecker.Rel` solves unification variables but computes no
logical guard. The contract is stated above `Rel.try_teq` in `Rel.fsti`:

* A problem (`Common.problem`) carries its context (`ctx_gamma`,
  `ctx_binders`), but no logical guard. The guards Rel returns always have
  `guard_f = Trivial`; they carry only deferred problems, universe
  constraints and implicits (`guard_of_solution`).
* Where relating two terms needs a proof, Rel succeeds when `wl.smt_ok`
  holds or when `env.admit` is set (`obligation_acceptable`). Core, which
  re-checks every term Rel helps elaborate, generates the obligation. The
  cases are:
  * subtyping between refinements, e.g. `x:int{x > 0} <: nat`;
  * narrowing a flex variable to a refinement (the meet or join of its
    bounds);
  * a head mismatch between heads that may be related by SMT
    (`may_relate_by_smt`), e.g. `f x == g x` for distinct `f` and `g`;
  * heads that only match after unfolding, in subtyping;
  * the branches of `match`es, and interpreted heads.
* Without SMT (`smt_ok = false`, the `_nosmt` functions) and outside
  admit mode, Rel succeeds only
  if the obligation simplifies to `True` (`simplify_vc true`).
* `Rel.try_subtype` replaces `get_subtyping_predicate`,
  `get_subtyping_prop` and `check_subtyping`. `TcUtil.weaken_result_typ`
  and `check_has_type` use `try_teq` / `try_subtype`.

So a client whose terms are not re-checked by Core must use the `_nosmt`
functions. These clients are `TcInductive`, `Positivity`, the tactic interpreter, and Pulse's `RuntimeUtils`.

Tactics that unify with guards allowed (`V2.Basic.__do_unify_wflags`) get
the obligation from Core: once Rel has solved the uvars, outside lax mode,
`Core.check_term_equality` relates the two terms and its guard becomes the
goal. If Core rejects them, the unification is rolled back and fails.

TcTerm still builds guards of its own (e.g. in `value_check_expected_typ`),
but it runs with `admit` set, and they are discarded.

## 4. What Core had to learn

Core used to serve tactics only (`core_check`) and only knew `Tot` and
`GTot`. To check everything the elaborator produces, it had to learn:

* **Effects.** `tot_or_ghost` became `eff = ETot | EGhost | EEff of lid`,
  with `join_eff` and `sub_eff`. An effectful computation (`Dv`, `ST`, a
  user effect) is opaque, and its result is a binder, never a term:
  * it is never substituted into a type;
  * an effectful `let` closes its variable existentially in the result
    type, as `TcUtil` does;
  * an effectful argument on which the type of the application depends is
    rejected;
  * as in `N.ghost_to_pure2`, `GTot` is promoted to `Tot` when it is lifted
    to, or composed with, an erasable effect
    (`micro-benchmarks/Erasable`).
* **Checking mode.** `check_against_typ` and `check_against_comp` push an
  expected type into `let`s, `match`es and `fun`s, as TcTerm does. Guards
  are then emitted where the relevant binders, path conditions and local
  lemmas are in scope. The SMT solver uses what it learns proving one
  conjunct to prove the next, so separating the two can make a proof fail.
  * A `fun` checked against an arrow has its body checked against the
    arrow's computation type (`abs_against_arrow`). The arrow may be behind
    an abbreviation, possibly ascribed. A `fun` may have more binders than
    the arrow, when its result is itself an abbreviation for an arrow.
    Refinements are never looked through for this.
  * The same applies to a `fun` passed as an argument whose formal type is
    an arrow.
  * The definition of a `let` is checked bidirectionally, in one pass
    (`check_let_def`). Without an annotation, its type is synthesized.
    With one, the definition is checked as follows, and then the annotation
    is checked to be a type. In that order, the well-formedness conditions
    that an annotation shares with those inside the definition (e.g.
    `j < length a` for a local lemma about `index a j` whose body binds
    another one) are emitted in the scope of the definition's goals, rather
    than closed over the annotation's binders and then dropped from the
    body as guard-cache hits (hacl-pulse `Spec.GF128.Poly.bits_inj`).
    * A pure or ghost definition is checked against it, so it is pushed
      into a definition that is a `let`, `match` or `fun`. For example, in
      `let f : t = (lemma (); f0) in e`, `f0` meets `t` under the lemma.
    * An effectful definition has its type synthesized and related to the
      annotation by subtyping. The postcondition of an effectful
      computation is carried only by its synthesized type, e.g. `n >= 0`
      after `if n < 0 then fail ""` (`FStar.Tactics.V2.Derived.repeatn`).
      Pushing the annotation would lose it.

    The choice uses `lb.lbeff`, the effect elaboration recorded for the
    whole `let`, which bounds the definition's. It only selects between
    two sound strategies.
  * Local `let rec`: the expected type is pushed into the body, which sees
    the recursive functions only through their types
    (`bug-reports/closed/Phase2CoreLetRecTail`).
  * The expected type is pushed through any stack of `Tm_meta` nodes.
* **Top-level APIs.** `check_term_at_comp`, `compute_term_comp` and
  `check_top_level_letrec`.
* **`let rec`**, inner and top-level, with termination as in TcTerm. An
  admitted termination check (`admit_termination`) still gives the other
  definitions the refined types. The `<<`-refined types are checked in the
  context of the nest, which catches ill-typed `decreases` clauses.
* **Local SMT lemmas.** `let f x : Lemma p [SMTPat t] = ... in e` makes the
  quantified lemma available in `e` (`smt_lemma_as_forall`), as
  `TcTerm.maybe_intro_smt_lemma` does.
* **`match`.**
  * Branch conditions use projectors and discriminators, applied to the
    scrutinee with the parameters and indices of its type
    (`inductive_type_args`), e.g. `TEq? #a #b #c s`, rather than a `match`
    on `s`, which the SMT solver knows much less about. This is done only
    for an indexed type; otherwise the parameters are the pattern's dot
    terms (looking up the type means normalizing it, which can be slow).
  * A pattern variable that a dot term mentions is replaced, in the branch
    condition, by the corresponding projection of the scrutinee
    (`pattern_var_projections`).
  * A `()` pattern has no branch condition.
  * The branch hypotheses (path condition, branch condition, equation
    between the scrutinee and the pattern) are separate implications, in
    that order, as tactics that address hypotheses by position expect.
  * `when` clauses are rejected (Error 236), as TcTerm rejects them.
  * One rule (`check_match`) checks every `match`, against a `returns t`
    annotation. The elaborator annotates every non-empty match
    (`TcTerm.elaborated_match_returns`): with the expected type, or with
    the result type of the branches; for an effectful match, that type is
    refined with `match sc with | p_i -> phi_i`, where `phi_i` is what the
    type of branch `i` says about the result (plus `x == b_i` for a pure
    `b_i` that may be returned). So whatever the continuation of the match
    needs to know is in its annotation, and Core no longer computes a type
    for a match from its branches.
  * A branch is checked against `t` with the *pattern* substituted for the
    `as` binder, as in `TcTerm.tc_eqn`
    (`bug-reports/closed/Phase2CoreReturnsAtPattern`). When `t` is a
    refinement by a `match` on the scrutinee with the same patterns as the
    match itself, the branch is checked against the formula of its own
    branch (`at_pattern`), rather than leaving the SMT solver to reduce the
    match.
  * A total or ghost `e` checked against `x:t{... /\ x == e /\ ...}` is
    checked against the rest of the refinement: the equation holds by
    reflexivity, which the SMT solver may not see, e.g. when `e` contains a
    lambda.
  * A `match` without an annotation (built by tactics, or by Pulse, e.g.
    its join of postconditions) is checked by the same rule against the
    expected type (e.g. the type of the formal it is passed to), else its
    residual type, else the type of its first branch, which must not
    mention the pattern's variables.
  * `match ... returns C` is checked like `returns t`, where `t` is `C`'s
    result type, plus a check of the effect.
  * The scrutinee's type is unrefined through any number of refinements and
    abbreviations before it is compared with a pattern's type.
  * Exhaustiveness is checked with the negated path condition, unless the
    patterns are syntactically exhaustive (e.g. a wildcard, or all the
    constructors of the scrutinee's type). Branches after a wildcard are
    checked as dead code.
* **Effectful `let`.** An effectful `let x = e1 in v`, with `v` pure, has
  the type `r:t{r == v}`, closed existentially over `x` when `v` mentions
  `x`. In `let x = e1 in e2` with `e1` pure and `e2` effectful, what `x`'s
  type says is kept in the type of the `let` when `x` does not occur in
  `e2`'s type.
* **Refinements** are typed `Type u`, even when their sort is an `eqtype`.
* **`let unfold x = e`** (`inline_let_vc`) substitutes `e` into the VC. So
  does every pure `let` under `--no_smt`.
* **`reflect`.** `M.reflect e`, checked against a computation type in `M`,
  checks `e` against the reification of that computation type.
* **Quantifiers without universes.** `l_Forall`/`l_Exists` as the
  desugarer produces them get the universe of their domain.
* **Equality ascriptions** `e $: t` relate `e`'s type to `t` by `EQUALITY`.
* **Ghost to total promotion.** A ghost computation checked against a
  non-informative type counts as total, and so does a ghost argument for a
  non-informative formal (`bug-reports/closed/Phase2CoreGhostArgNonInfo`).
* **Eta.** `fun x -> e` relates to a non-abstraction `t` by relating `e` to
  `t x` under the binder, in both directions.
* **Unfolding.** When the delta-unfoldings of two applications never come
  to have the same head, the guard is stated on the terms as they were, so
  that the SMT patterns of lemmas about them fire. The same holds when one
  side is a variable (`examples/metatheory/StlcCbvDbParSubst`). In that
  case, Core also normalizes the other side once to head normal form,
  unfolding recursive definitions, and compares without a guard
  (`closes_with_zeta`; `bug-reports/closed/Bug3207b`). Recursive
  definitions are not otherwise unfolded, which would loop
  (`bug-reports/closed/Bug606`).
* **Equations between applications.** When two applications with the same
  head cannot be related without a guard, relating the arguments and
  relating the unfoldings are each sufficient, but neither is necessary.
  Core emits the disjunction (`either_guard`). With `natlt n = i:nat{i <
  n}`, `natlt i <: natlt n` gives `(x < i ==> x < n) \/ i == n`
  (FStarLang/FStar#4239). Exceptions:
  * an equation whose arguments are, or contain, abstractions, arrows or
    refinements: the arguments are related first, and the unfoldings only
    if that fails. The SMT encoding keys such binders on their free
    variables, so an equation between the whole terms is seldom provable;
  * subtyping, e.g. `st pre post <: st pre' post'`: the unfoldings are
    related by implications;
  * heads marked `[@@unifier_hint_injective]`, e.g. LowParse's `parser k
    t`, as in Rel (`bug-reports/closed/Phase2CoreKindByEval`);
  * a quantifier-free guard of the unfoldings is taken on its own rather
    than in a disjunction, which makes Z3 case-split.
* **Folded or unfolded guards.** An abstraction or a refinement is encoded
  as a fresh symbol keyed on its free variables, so two such terms are only
  provably equal when they are syntactically equal. Core therefore picks
  the form of a guard:
  * unfolding that reaches a `match` or a `fun` on one side while the other
    is still an application gives a guard on the folded terms, unless that
    application has no definition (e.g. `p ** q`);
  * unfolding that reaches a refinement is kept only if the refinement's
    base comes to have the same head as the other side, e.g. `nat` against
    `int` (`bug-reports/closed/Phase2CoreBranchTypeByUnfolding`,
    `Phase2CoreFoldedRefinements`);
  * a recursive head is unfolded only if that closes the relation without
    a guard, or when relating it to a `match`;
  * a `match` whose scrutinee only reduces after unfolding is evaluated
    (`UnfoldUntil delta_constant`), and the result is kept only if a branch
    is taken (`bug-reports/closed/Phase2CoreStuckMatchByEval`);
  * when neither side unfolds and one of them is a literal, both sides are
    evaluated.
* **Residual types of function literals.** The unifier may copy a function
  literal with different residual types. The SMT encoding keys the
  literal's token on its residual type, so Core unrefines these types in
  its guards, unless the body is ascribed a refinement type
  (`bug-reports/closed/Phase2CoreAscribedResidual`).
* **No unification or elaboration inside Core.** Core does not depend on
  Rel, TcTerm or TcUtil (see "Dependencies" in the header of
  `FStarC.TypeChecker.Core`). It equates universes with
  `UnivEq.teq_univs`, Rel's universe solver without the worklist; an
  unsatisfiable universe constraint is a failed comparison. The
  `<<`-refined types of a `let rec` are built by
  `Termination.guard_letrecs` with fresh universe variables for `precedes`
  and `===`, which Core solves when it checks those types. The utilities
  it shares with the elaborator are in `VCUtil`, `UniverseOf`,
  `Termination` and `CommonBase`.

## 5. Guards and facts

TcTerm binds every sub-computation to a name of its (refined) type, so what
that type says is in scope for everything after it. Core synthesizes the
type of an application as the head's result type, which says nothing about
the arguments. Core instead recovers the missing information as **facts**:

* Facts are computed by `do_check` in the same pass as a term's type, from
  the facts of its subterms, and are cached with the type (`facts`). They
  are lazy (`Thunk`), since most are never used. No term is traversed or
  checked again to compute them.
* `f_sub` holds the facts about a term's subterms: an application's
  arguments, the definitions of the `let`s it is made of (with a pure
  definition substituted for its variable, and the facts mentioning the
  variable of an effectful one dropped), and its branches, each under the
  condition that its branch is taken. The facts of the second argument of a
  short-circuiting operator are stated under the first argument's
  condition.
* `f_term` holds what a pure term's type says about it (`term_facts`),
  together with `f_sub`. A term checked against an expected type (a pushed
  `let` or `match`) gets its facts from that type, plus its `f_tail`, which
  stands in for what its unsynthesized type would have said: for example,
  the `squash p` of `lemma ()` in a branch `(lemma0 (); lemma ())` checked
  against `unit`.
* `f_tail` holds the `f_term` of the expression that a term's `let`s end
  with.
* Facts are added as hypotheses of the guard at a refinement-subtyping
  witness (`witness_guard`), of the subtyping of an argument whose formal
  depends on earlier arguments (`check_app_arg`), and when a pure `let` is
  closed.
* The result type of an application of a top-level function contributes a
  fact only when it is syntactically a refinement or a squash. A name that
  unfolds to a refinement (e.g. `pos`) contributes none: the function's
  typing axiom already gives that fact, and repeating it at every use adds
  nonlinear hypotheses that derail the solver.
* Atomic terms contribute no facts, except a top-level name whose type is
  `squash p` (e.g. a lemma used as a value): its fact is `p`.
* A branch's facts that do not mention its pattern variables are stated as
  `cond ==> facts`, without a quantifier.

A pure `let x = e1 in e2` closes its guard as `forall x. x == e1 ==> facts
==> phi`, simplified as follows:

* The defining equation is dropped when it is useless (`def_eq_useful`, the
  analogue of `TcUtil.should_return`).
* The quantifier is dropped when, in addition, `x` is not free in `phi`. A
  useful equation is kept: it may trigger an SMT pattern.
* Only the facts about the subterms of `e1` are added when `x` is already
  quantified at its own type.
* A vacuous quantifier over a *null* `unit` binder is dropped, as by
  `Env.close_guard`. Named `unit` binders (e.g. of `calc` step thunks) are
  kept: the SMT encoding assumes each quantifier-free conjunct of a guard
  while proving the next (`ErrorReporting.split_goals`), so dropping them
  would put every earlier `calc` step into the context of every later one.
* When `x` is not quantified and the `let` is annotated, what the
  annotation says about `e1` is added as a fact, before `e1`'s own facts.

The variable `x` is bound at the annotation of the `let`, or else at the
type synthesized for `e1` (`let_binder_sort`). The universe of a
synthesized type is computed without checking that type again
(`universe_of_well_typed_term`). When `e1`'s type was also synthesized for
an annotated `let` (an effectful `e1`, or one into which the annotation is
not pushed), its refinement is added to `x`'s type: the annotation may be
one that elaboration inferred, which lacks the definition's postcondition.
When the annotation is pushed into a pure `e1`, what `e1` establishes
beyond its annotation reaches the body as facts: those of `e1` and its
subterms, and those of the expression that the `let`s of `e1` end with
(`f_tail`). For
example, `eliminate exists x. p x with lemma x` elaborates to
`let _ : unit = (let x = .. in lemma x) in ..`, where only the type of
`lemma x` says what it proves
(`PulseCore.IndirectionTheoryActions.witness_exists`).

For a top-level `let rec`, the driver binds the names of the nest before
the binders (`is_nest_name`). The SMT encoding closes a query only over the
variables at the end of the environment and encodes the others as
constants, so a refinement over the binders would otherwise be encoded
differently from the typing axiom of the recursive function
(`FStar.List.Tot.Base.list_refb`).

**The guard cache.** Core memoizes types and guards. A guard found in the
cache whose context includes the current one is treated as already
emitted. A caller that transforms the guard of a sub-computation (closing,
weakening, adding facts) must re-emit it with `reemit_guard`, not `guard`.
Otherwise a trivial transformation hits the cache entry the
sub-computation just inserted, and the guard is silently dropped, which is
unsound. `quietly` drops the guard of a computation that has already been
checked, and keeps the cache only when there was no guard. The memo table
is cleared around every elaboration (`Tc.elaborating`,
`CoreCheck.elaborate`), since Core may run on unproven terms there.

## 6. What `.checked` files record

A client of a module sees the module's sigelts. For an unannotated
definition, that includes **the type recorded in `lbtyp`**. Unification in
a client compares the heads of the indices of that type, e.g. `raw a
(U32.add l1 l2)` against `raw a (l1 + l2)` ("head mismatch" in `Rel`). So
the recorded type must be stable, not merely equivalent to some other
valid type. Otherwise dependents fail with elaboration errors (Error 54 or
189) far from the change.

This is why Core checks against the type elaboration inferred (§1), and
that is the type recorded. Core's own inferred types (`--ext core_infer`)
differ in hundreds of places over `ulib`: abbreviations unfolded (`u32`
becomes `U32.t`), refinements typed as `eqtype`, unnormalized `unfold`
operators.

Tests run with `--cache_off` elaborate their dependencies from source in
lax mode, so they cannot catch this class of problem. Build real `.checked`
files to test changes that affect recorded types.

## 7. Known limitations

* **Error reporting.** Core labels its guard as TcTerm labelled its own, so
  that a failed goal is reported with a similar message, range and
  context:
  * the subtyping of a term at a type is labelled "Subtyping check failed"
    at the term, with "Expected type ... got type ...", except for `()`
    given for a `squash p`, which only locates the goal
    (`label_subtyping`);
  * the body of a function checked against an arrow is labelled at the
    abstraction with "Could not prove post-condition"
    (`label_postcondition`), and each binder's annotation with "Type
    annotation on parameter incompatible with the expected type";
  * the obligations of a formal type, e.g. the termination refinement of a
    recursive call, are located at the argument;
  * branch conditions are the negation of the earlier patterns and the
    pattern's own condition, then the scrutinee's equation; the
    exhaustiveness obligation is labelled at the match;
  * the refinement of the domain of an arrow is a hypothesis of the guard
    of its codomain, not the sort of its quantifier.

  Core's VCs differ from those TcTerm used to generate, and some expected
  outputs show it (`tests/error-messages`: `Calc`, `Coercions`,
  `ShortCircuiting`, `PatAnnot`, `FunctionalExtensionality`,
  `TestErrorLocations`):
  * Core's VC carries more facts (§5), which show in the context of a
    failed goal, and may prove more;
  * a failure to relate two applications reports the disjunction of
    `either_guard`;
  * the failed annotation of a pattern binder is a subtyping failure at the
    binder;
  * the obligation of a `calc` step's proof is located at the step, not at
    its relation.
* **Not handled.** Core rejects `when` clauses (Error 236) and `match ...
  returns` annotations with tactic handlers.
* **Elaborated terms.** Terms that tactics inspect and that are printed are
  the elaboration. It annotates every non-empty `match` with a `returns`
  type (see above), which is printed, and it creates fewer fresh names
  than a second TcTerm run did (`error-messages/TuplePat`, `Monoid`,
  `ide/emacs/Fib.compute`, `tactics/Postprocess`, `tests/tactics/DeltaDepth`).
* **Brittle proofs.** A proof close to its rlimit may flip, because Core's
  VCs are shaped differently from TcTerm's former ones. The SMT encoding
  proves each conjunct of a guard assuming the quantifier-free conjuncts
  before it (`split_goals`), so the quantifiers Core keeps or drops change
  the context of each goal (§5). A proven conjunct that is not
  quantifier-free contributes its quantifier-free parts. A conjunct
  mentioning a definition whose body is quantified is not assumed
  ([#4615](https://github.com/FStarLang/FStar/issues/4615)), unless the
  query already assumes that same atom, e.g. as a conjunct of a
  precondition or of an implication's premise: then the solver has its
  quantifier anyway, and dropping the atom only made re-proving a lemma's
  own precondition (e.g. for a call) harder. Proofs
  adjusted for this include `FStar.Math.Lemmas` (`modulo_sub_lemma`,
  `lemma_mod_plus`, `lemma_div_plus`), `FStar.Math.Fermat`,
  `FStar.UInt<N>.eq_mask`/`gte_mask`, `Quicksort.Base.lemma_sorted_append`,
  `BoolRefinement.rename_elab_binding_denote`, `CborBoundary.item`,
  `Pulse.Lib.PriorityQueue` and `Pulse.Lib.HashTable.Spec`.
* **Pulse.** Pulse calls Core directly, so the labels above show in the
  expected output of Pulse's failures (e.g. `pulse/test/Test.Recursion`,
  `bug-reports/{Bug59,Bug94,Bug100,Bug206}`): an argument that does not have
  its formal's type is reported as "Subtyping check failed" at the
  argument, and a termination obligation at the decreasing argument.

## 8. Debugging

* `--debug Elab` prints the elaboration of each definition, the expected
  type given to Core, and the guard the driver discharges.
* `--debug CoreTop` prints each top-level query and its simplified guard.
* `--debug Core` traces the checker; `CoreEq` traces its equality checks,
  and `CoreExit` its results.
* `--debug CoreFacts` shows the facts collected at each witness and `let`.
* `--debug DisableCoreCache` turns memoization off. Use it to rule out cache
  bugs.
* To tell an elaboration problem from a Core problem, check the module with
  `--admit_smt_queries true`: that only elaborates.

## 9. Performance

When Core replaced TcTerm as the VC generator, checking the 20 largest
`ulib` modules from source took about 5% longer in total, from -6%
(`FStar.Math.Lemmas`) to +27% (`FStar.Reflection.TermSpec.Lemmas`) by
module. Peak memory was unchanged. With `--admit_smt_queries true` the
times were within 3%: memoization makes Core about as fast as TcTerm's VC
generation was, despite the facts it collects.

Much of the remaining difference is not in the VCs themselves but in the
state of the long-lived z3 process. F\* reuses one z3 process for a whole
module, so perturbing the earlier queries changes how long later ones
take. For example, `FStar.Rational.m4` took 0.18s before and 1.58s after
when the whole module was checked, for an identical query that takes 0.09s
when checked alone. Use `--z3refresh` (a fresh z3 for every query) to
compare the time of individual queries.

Real slowdowns exist where Core's VC is split differently: in
`FStar.Seq.Permutation.foldm_snoc_split'`, Core sends 43 larger goals
where TcTerm sent 81 smaller ones.
