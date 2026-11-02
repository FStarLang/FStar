# Typechecking with Core

*A reference for F\* compiler developers.*

`FStarC.TypeChecker.Core` is the only generator of verification conditions
(VCs) in F\*. Every term of a top-level declaration is checked in two
steps:

1. **Elaboration.** `TcTerm` runs once, with `env.admit` set. It infers
   implicit arguments, universes and types, inserts coercions and monadic
   annotations, and runs the tactics that produce terms. It proves nothing:
   the guards it builds are discarded. The result is a fully elaborated
   term with no unification variables.
2. **Checking.** Core checks the elaborated term as it is, and computes its
   VC, which is discharged by the SMT solver (or by tactics).

Core is a checker, not an elaborator. It does no unification and no
inference of implicits, and it does not depend on `Rel`, `TcTerm` or
`TcUtil`. It is a small, self-contained basis for a more trustworthy core
of F\*.

The unifier, `Rel`, is part of elaboration. It solves unification variables
but computes no logical guard (§4).

Core builds on the simplified effect system (see
[simplified_effect_system.md](simplified_effect_system.md)). `Tot`, `GTot`
and `Div` are primitive, and specifications live in refinements rather than
in WPs, so Core distinguishes only three kinds of computation: `ETot`,
`EGhost`, and an opaque *effectful* `EEff m`.

In lax mode (a lax module, `--admit_smt_queries true`, or while
elaborating), `env.admit` is set and Core does not run: terms are only
elaborated (`CoreCheck.enabled`, `CoreCheck.check_or_elaborate`).

Contents:

1. [Code layout](#1-code-layout)
2. [The driver for `let`](#2-the-driver-for-let)
3. [Declarations other than `let`](#3-declarations-other-than-let)
4. [Rel as an elaborator](#4-rel-as-an-elaborator)
5. [What Core requires of an elaboration](#5-what-core-requires-of-an-elaboration)
6. [The checker](#6-the-checker)
7. [Guards, facts and caches](#7-guards-facts-and-caches)
8. [Error reporting](#8-error-reporting)
9. [What `.checked` files record](#9-what-checked-files-record)
10. [Known limitations and open questions](#10-known-limitations-and-open-questions)
11. [Debugging](#11-debugging)
12. [Performance](#12-performance)

---

## 1. Code layout

The checker lives in `src/typechecker`. Each support module has a
documented interface, and depends only on the modules above it:

| module | contents |
|---|---|
| `Core.Base` | Debug toggles, effects (`eff`), the environment (`env`), facts, relations, error contexts and errors. |
| `Core.Monad` | The `result` monad: a computation runs in a context, threads the functional cache, and fails or succeeds with an optional guard. Also its combinators (`with_context`, `handle_with`, `no_guard`, `quietly`, ...). |
| `Core.Binders` | The initial environment; opening binders, terms, patterns and branches, with deterministic names (§7). |
| `Core.Effects` | The effect lattice as Core sees it (`join_eff`, `sub_eff`, ...). |
| `Core.Util` | Utilities on terms, types and patterns that do not call back into the checker (e.g. `let_binder_sort`, `pat_field_projection`). |
| `Core.Facts` | The facts Core gathers about terms and assumes in guards (§7). |
| `Core.Cache` | The term and guard caches, and the memo of failed relations. |
| `Core.Guard` | Emitting guards, and closing, weakening and labeling them. |
| `Core` | The checker proper, then the public API. |

The checker proper is one mutually recursive definition, in sections:
relating types; checking terms; types, universes and computation types;
checking against an expected type; `let`; `let rec`; and `match`. The
header of `Core.fst` summarizes the layout and the caches.

Core shares a few small modules with the elaborator: `VCUtil` (labels and
simplification of VCs, `synth_proof_goal`), `UnivEq` (Rel's universe
solver without the worklist), `UniverseOf` (types of constants, syntactic
universe computation), `Termination` (the `<<`-refined types of recursive
definitions) and `CommonBase`. A few `Env` callbacks (e.g.
`env.typeof_well_typed_tot_or_gtot_term`, used by `Termination`) dispatch
to TcTerm at runtime, only to compute terms that Core then checks.

`FStarC.TypeChecker.CoreCheck` is the interface the rest of the type
checker uses (§3).

## 2. The driver for `let`

The driver is `Tc.tc_sig_let`, with `Tc.tc_sig_let_core`.

* **Elaboration.** TcTerm runs with `admit` set, inside `Tc.elaborating`,
  which clears Core's memo table before and after (the elaboration's
  guards are not proven, so nothing Core caches meanwhile may be trusted).
  In a lax module the driver stops there, after
  `CoreCheck.check_smt_patterns` (§3).
* **Non-recursive `let`.** The elaborated definition is checked with
  `Core.compute_term_comp` against an expected type:
  * the user's annotation, if there is one;
  * otherwise, **the type elaboration inferred**. The elaborator's
    type is dropped from the definition and remembered (`drop_lbtyp`,
    `elab_lbtyp`).

  Core does no inference, even at the top level: clients depend on the
  recorded type (§9). With `--ext core_infer`, Core infers the type
  instead.

  Declared types are checked for well-formedness on their own first
  (`check_declared_types`), and their guard is discharged as a separate
  query. Core caches what it proves, so checking the definition does not
  emit that guard again. In one guard, the type's conjunct, quantified over
  its binders, would be a hypothesis of every goal of the definition (§7,
  `split_goals`), which derails the SMT solver, e.g. with nonlinear terms
  like `pow2 (hi - lo)`. This applies to the user's annotation, to the
  declared types of a recursive nest, and to the elaborated type of a
  definition whose result is annotated, as in `let f x : Lemma (requires p
  x) (ensures q x) = e` (`result_annotated`).

  An inferred type is not checked (`check_t = false`): it may only be
  well-formed in the context the definition sets up, e.g. `x:U32.t{v x = f
  b}` for `let n = f b in lem b; U32.uint_to_t n`, where `=` is taken at
  `uint_t 32`.

  An inferred computation type is normalized as TcTerm normalizes the
  computation type of a function body (`Beta; Eager_unfolding; NoFullNorm;
  Exclude Zeta`): only the result of the arrow, not its binders.

  Core's guard is then discharged by `tc_sig_let_core` (`discharge`), and
  the definition is finished by `TcTerm.finish_top_level_let` with a
  trivial guard: it masks top-level effects, checks that the type is
  inhabited, applies tcnorm, and closes the universes.
* **Recursive `let`.** `Core.check_top_level_letrec` replaces the
  top-level names of the nest by fresh variables and checks the nest as an
  inner `let rec` (§6.6). The names are substituted back into the guard.
  The driver binds the names of the nest *before* the binders of the
  function when it discharges the guard (`is_nest_name`): the SMT encoding
  closes a query only over the variables at the end of the environment and
  encodes the others as constants, so a refinement over the binders would
  otherwise be encoded differently from the function's typing axiom
  (`FStar.List.Tot.Base.list_refb`).
* **Discharging.** The guard is simplified (`Rel.simplify_guard`) before it
  is discharged, as TcTerm simplifies the guards it builds. This matters
  for normalization requests: in `norm [nbe; primops] ("a" ^ "b") == "ab"`,
  the simplifier reduces the argument's primitive application first,
  whereas the request itself, with only `primops`, does not unfold `(^)`.
  The leading quantifiers of the guard, e.g. over the binders of `let f x y
  = ...`, are opened into the environment (`open_foralls`), so that the
  goal, the context of a failure, and tactics such as `handle_smt_goals`
  see the binders as hypotheses (`examples/tactics/HandleSmtGoal`). The
  guard of a function body is discharged at the range of the body.
* **Synthesized proofs.** Once Core has accepted a definition, the
  `synth_by_tactic` applications at proof goals in it (§6.9) are replaced
  by `()` (`Tc.erase_synthesized_proofs`) before it is recorded.
* **Failures.** Only Core decides whether a definition is accepted.
  * An unprovable guard is reported by the SMT solver, with the labels and
    ranges Core puts on it (§8).
  * A structural failure is reported with Core's error. Where TcTerm has an
    error code for the same failure, Core's error carries it
    (`Core.error_code`) and is reported with it and TcTerm's message: Error
    34 for a computation of the wrong effect (e.g. `GTot` for `Tot`), Error
    236 for a `when` clause. Any other structural failure is Error 12,
    "Core failed to check this definition", followed by Core's context, and
    located at the innermost term of that context (`Core.error_range`).
  * An elaboration with free names is rejected with Error 327
    (`Error_IllScopedTerm`); see §5.

## 3. Declarations other than `let`

Core checks every term of a declaration whose checking matters for
soundness. Each term is elaborated with `admit` set, and Core checks the
elaboration. The common part is in `FStarC.TypeChecker.CoreCheck`:

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
| `assume` (`Sig_assume`) | The same, but the formula must have type `prop`. In Prims, `prop` is an `assume val`, not `Type`, so `universe_of` would reject it. |
| inductives (`Sig_bundle`, `TcInductive`) | The bundle is elaborated with `admit`; then `TcInductive` runs again on the elaboration, and checks its terms with Core: the parameters, indices and kind of each type (`check_or_elab_binders`, `check_or_elab_type`), the arguments and result type of each constructor (`check_or_elab_tparams`), the binders of the injectivity-on-parameters check, and the hasEq formula against `prop`. A `val` that predeclares an inductive must agree with it (`Core.check_term_equality`). |
| projectors, discriminators, hasEq axioms | Generated as `val`s, `let`s and `assume`s, and checked through those paths. A projector's type takes the type's parameters as implicit arguments of the projections of earlier fields. |
| effects (`TcEffect`) | Every combinator is elaborated, then checked by Core against its expected type (`check_comb`). Core also computes the universe of a representation (`repr_universe`). |
| `sub_effect` | The lift is elaborated (`tc_lift` with `admit`, then `elim_uvars`), so that the terms Core checks are closed. |
| attributes | Elaborated, then Core computes their types (`Tc.tc_decl_attributes`). |
| implementation vs. interface `val` | `check_subsumes_iface_val` asks Core whether the implementation's type is a subtype of the interface's (`CoreCheck.check_subtyping`). |
| `[@@no_subtyping]` | Core checks the type with `use_eq_strict` set, in which `Core.check_relation` checks `EQUALITY` where it would check `SUBTYPING`. Core accepts lemmas (`int : eqtype` vs `Type`) and rejects actual subtyping, e.g. `nat` for `int` (`tests/bug-reports/closed/Phase2CoreNoSubtyping`). |
| `%splice` tactics (`Hooks.splice`) | The tactic is elaborated; Core checks it against `dsl_tac_t` (typed splices) or `unit -> Tac decls`. |
| tactics run by the interpreter (`Interpreter.run_tactic_on_ps`) | When the tactic is not already typed, e.g. in `assert ... by`, `synth_by_tactic` or `postprocess_with`, it is elaborated (`TcTerm.tc_tactic`), and Core checks it against `a -> Tac b`. |
| `#check` | The term is elaborated, and Core checks it at the inferred computation type (`Core.check_term_at_comp`). Core's guard is shown, not discharged. |
| `#eval` | Core computes the computation type of the elaboration (`Core.compute_term_comp`). The guard is not discharged. |
| `__tc`, `__tc_ghost` (`V2.Basic.tc_with_core`) | TcTerm elaborates with `admit`; Core computes the type and the guard, which becomes a goal. |

**SMT-pattern warnings.** Core does not emit Warning 271 (a pattern that
misses a bound variable, or uses theory symbols).
`CoreCheck.check_smt_patterns` walks the arrows of what was checked
(`val`/`assume` types, `let` bodies, constructor arguments) and calls
`TcTerm.check_smt_pat` on them, in lax mode too. So that the patterns of
lemma types have no uvars, `Normalize.norm_comp` processes the `SMTPAT`
flag when `compress_uvars` is set
(`tests/bug-reports/closed/Phase2CoreLemmaPatterns`).

**Terms not checked again.** These are justified otherwise:

* The result of postprocessing (`postprocess_with`,
  `postprocess_for_extraction_with`) is justified by the equality proof the
  tactic must produce.
* Typed splices that claim their result is already checked
  (`checked = true`, e.g. Pulse) are trusted. This rests on the type of
  the splice tactic, `dsl_tac_t`, which Core checks.

## 4. Rel as an elaborator

`FStarC.TypeChecker.Rel` solves unification variables but computes no
logical guard. The contract is stated above `Rel.try_teq` in `Rel.fsti`:

* A problem (`Common.problem`) carries its context (`ctx_gamma`,
  `ctx_binders`), but no logical guard. The guards Rel returns always have
  `guard_f = Trivial`; they carry only deferred problems, universe
  constraints and implicits (`guard_of_solution`).
* Where relating two terms needs a proof, Rel succeeds when `wl.smt_ok`
  holds or when `env.admit` is set (`obligation_acceptable`), and Core,
  which checks every term Rel helps elaborate, generates the obligation.
  The cases are:
  * subtyping between refinements, e.g. `x:int{x > 0} <: nat`;
  * narrowing a flex variable to a refinement (the meet or join of its
    bounds);
  * a head mismatch between heads that may be related by SMT
    (`may_relate_by_smt`), e.g. `f x == g x` for distinct `f` and `g`;
  * heads that only match after unfolding, in subtyping;
  * the branches of `match`es, and interpreted heads.
* Without SMT (`smt_ok = false`, the `_nosmt` functions) and outside admit
  mode, Rel succeeds only if the obligation simplifies to `True`
  (`simplify_vc true`).
* `TcUtil.weaken_result_typ` and `check_has_type` use `Rel.try_teq` /
  `Rel.try_subtype`.

A client whose terms Core does not check again must therefore use the
`_nosmt` functions: `TcInductive`, `Positivity`, the tactic interpreter,
and Pulse's `RuntimeUtils`.

Tactics that unify with guards allowed (`V2.Basic.__do_unify_wflags`) get
the obligation from Core: once Rel has solved the uvars, outside lax mode,
`Core.check_term_equality` relates the two terms and its guard becomes a
goal. If Core rejects them, the unification is rolled back and fails.

TcTerm still builds guards of its own (e.g. in `value_check_expected_typ`),
but it runs with `admit` set, and they are discarded.

## 5. What Core requires of an elaboration

Nothing re-elaborates the elaborated term. It is what Core checks, and what
is recorded, extracted and reified. So it must be closed and complete.

### Ill-scoped elaborations

The elaboration must be closed: Core checks it as it is, so an elaboration
with free names is
rejected (Error 327, an internal error). Rel maintains the invariant that
every occurrence of a uvar is in the scope of its whole context, except for
the names its delayed substitution maps: `Rel.ensure_no_uvar_subst` may
solve `?u` as `?v x1 .. xn` over the suffix of its context that a
substitution affects, and an occurrence of `?u` outside the scope of some
`xi` would then have `xi` free. The places that must respect it:

* **Branches.** A branch is checked without the match's logical scrutinee
  `guard_x`, which is never bound in the term when the scrutinee is pure;
  the pattern's guard and the branch's equations add it to their own
  environments (`TcTerm.tc_eqn`, `scrutinee_env`; `examples/typeclasses/Eq`).
* **Eta-contraction** in `Rel.mk_solution`: `?m x =?= h e x` is solved with
  `?m := h e` only after restricting the uvars of `h e` to the binders it
  still abstracts over; the contraction is refused if `x` occurs in the
  type of such a uvar (`tests/custard/Mymon`).
* **Types escaping a binder.** The result type of `let x = e1 in e2`, or of
  a branch, is used outside the scope of `x` or of the pattern's variables.
  `Rel.restrict_escaping_uvars` restricts every uvar in it to its context
  minus the escaping names (and the binders whose sorts depend on them),
  for a `let` (`TcUtil.composite_result_typ`) and for a branch
  (`TcTerm.tc_eqn`). A uvar whose type mentions an escaping name is left
  alone.
* **`Rel.restrict_ctx`**, solving `?m y =?= e`, restricts each uvar `?s` of
  `e` to the part of its context shared with `?m`'s, plus `y`, also
  abstracting over the dropped binders `?s`'s type depends on
  (`Pulse.C.Types.Scalar.read_prf`).

### Complete elaborations

The elaboration must carry everything a checked term carries.

* **Types of inner `let`s.** `TcTerm.check_inner_let` records the inferred
  type of every unannotated inner `let`, since Core needs a type on every
  binder. That type must be right: Rel joins the lower bounds of a flex
  variable only if they share a base type (`lower_bounds_share_a_base`;
  `tests/bug-reports/closed/Phase2CoreJoinBases`).
* **Monadic annotations.** `Meta_monadic`, `Meta_monadic_lift` and `lbeff`
  follow the rule of `check_inner_let`: the definition is lifted to the
  effect of the whole `let`, which is also its `lbeff`. This holds for the
  `let`s TcTerm inserts too: for an impure scrutinee (`tc_match`), for
  effectful arguments (`bind_lifted_args`), and for short-circuit operators
  with an effectful operand, which are rewritten to `if` and checked again
  (`maybe_elaborate_short_circuit_args`; `tests/custard/plugin`).
* **`match` annotations.** Every non-empty `match` the elaborator produces
  has a `returns` annotation (`TcTerm.elaborated_match_returns`): the
  expected type, or the result type of the branches. For an effectful
  match, that type is refined with `match sc with | p_i -> phi_i`, where
  `phi_i` is what the type of branch `i` says about the result (plus `x ==
  b_i` for a pure `b_i` that may be returned). The unused pure `let`s of
  `b_i`, e.g. `assert p;`, are dropped from it (`drop_unused_pure_lets`):
  `p` may rely on facts, e.g. an `assume`, that do not hold where the
  annotation is checked. So whatever the continuation of a match needs to
  know is in its annotation (§6.7).
* **Synthesized terms.** `synth_by_tactic` at a type that is not a proof
  goal runs during elaboration, and its result is left in the elaborated
  term, as the tactic wrote it, without an ascription (clients and tactics,
  e.g. `def_of` in `examples/tactics/Normalization.fst`, see it as
  written). A goal may mention uvars that are solved only after the tactic
  would run: in `f h (_ by tac)`, the implicits of `f` may wait on the
  deferred subtyping of `h`. So a definition that mentions
  `synth_by_tactic` is elaborated twice: first without synthesis, then
  with it (`TcUtil.with_synth`), over the first elaboration, whose goals
  are resolved. Other callers of TcTerm do not run synthesis
  (`TcUtil.synth_mode`; see §10). Proof goals are left to Core (§6.9).

## 6. The checker

Core's judgment is `g |- e : E t | p`: in environment `g`, `e` has effect
`E` and type `t`, provided the guard `p` holds in `g`. `check` synthesizes
`E t`; `check_against_typ` and `check_against_comp` check `e` against an
expected type or computation type. Each also returns the facts about `e`
(§7).

### 6.1 Effects

`eff = ETot | EGhost | EEff of lid`, with `join_eff` and `sub_eff`. An
effectful computation (`Dv`, `ST`, a user effect) is opaque, and its result
is a binder, never a term:

* it is never substituted into a type;
* an effectful `let` closes its variable existentially in the result type
  (§6.5);
* an effectful argument on which the type of the application depends is
  rejected.

As in `N.ghost_to_pure2`, `GTot` is promoted to `Tot` when it is lifted to,
or composed with, an erasable effect (`micro-benchmarks/Erasable`). A ghost
computation checked against a non-informative type counts as total, and so
does a ghost argument for a non-informative formal
(`bug-reports/closed/Phase2CoreGhostArgNonInfo`).

`M.reflect e` checked against a computation type in `M` checks `e` against
the reification of that computation type. `reify e` has the representation
type, in `GTot` for a primitive extraction, in `Tot` for a total effect,
and in `Div` otherwise.

### 6.2 Checking against an expected type

Core is bidirectional: it pushes an expected type into the term, as TcTerm
does, so that guards are emitted where the relevant binders, path
conditions and local lemmas are in scope. (The SMT solver uses what it
learns proving one conjunct to prove the next; separating the two can make
a proof fail.) The expected type is pushed into:

* a non-recursive `let` (into its body) and a `let rec` (into its body,
  which sees the recursive functions only through their types;
  `bug-reports/closed/Phase2CoreLetRecTail`);
* an unannotated `match` (§6.7);
* any stack of `Tm_meta` nodes over the above;
* a `fun` checked against an arrow (`abs_against_arrow`): each binder's
  annotation is related to the arrow's domain (labeled "Type annotation on
  parameter incompatible with the expected type"), and the body is checked
  against the arrow's computation type (`label_postcondition`). The arrow
  may be behind an abbreviation, possibly ascribed, and a `fun` may have
  more binders than the arrow when its result is itself an abbreviation for
  an arrow. Refinements are never looked through for this.

Any other term has its type synthesized and related to the expected type
by subtyping (`check_against_typ_by_subtyping`); for a pure term, the
subtyping has the term as its witness, so the guard can mention it, and
assumes its facts (`witness_guard`). The guard is labeled at the term
(`label_subtyping`, §8).

`check_against_typ_synth` also returns the synthesized type when it had
to synthesize one. Checked against `x:t{... /\ x == e /\ ...}`, a total or
ghost `e` is checked against the rest of the refinement (`drop_self_eq`;
the equation is `TEQ`-equal, or `term_eq` up to `Meta_monadic`): the
equation holds by reflexivity, which the SMT solver may not see, e.g. when
`e` contains a lambda. If the result is not total or ghost, it is checked
again against the full type.

Ascriptions: `e <: t` checks `e` against `t`; `e $: t` relates `e`'s type
to `t` by `EQUALITY`; `e <: t by tac` is §6.9.

### 6.3 Applications

Each argument is checked against its formal with `check_against_typ_synth`
(so an expected type is pushed into a `fun` or `match` argument), with the
formal's use range set to the argument: the obligations of the formal type,
e.g. the termination refinement of a recursive call, are located at the
argument. When the formal is dependent and the argument is not atomic, the
argument's facts are added to the guard (`with_deps`), as TcTerm binds the
argument to a name of its type.

For the short-circuit operators (`VCUtil.short_circuit_head`: `&&`, `||`,
`/\`, `\/`, `==>`, `ite`), the second argument is checked under the first's guard
formula, and its facts are stated under that condition.

### 6.4 Relating types

`check_relation g rel t0 t1` decides `EQUALITY` or `SUBTYPING` (with an
optional witness term and its facts), possibly with a guard. In a context
that allows no guard (`no_guard`), it fails instead of emitting one.

* Terms equal up to `TEQ` are related. Universes are equated by
  `UnivEq.teq_univs`; an unsatisfiable universe constraint is a failed
  comparison. Metas and ascriptions are stripped.
* `squash p <: squash q` is the guard `p ==> q`.
* Refinement against refinement with matching base heads relates the
  bases, then emits the implication of the refinements (over the witness,
  if any). Without guards, normalized equality is tried instead. Refinements
  are typed `Type u`, even when their sort is an `eqtype`.
* Arrows: the domains contravariantly (by `EQUALITY` when relating by
  equality), the computation types under the binder. A refined domain `y:t{phi}` is
  quantified at `t`, with `phi` a hypothesis (`with_binder_unrefined`), as
  TcTerm's guards for arrow domains are.
* Abstraction against abstraction: domains and bodies by `EQUALITY`.
* Abstraction against a term that is not one: the latter is unfolded, as in
  Rel's `head_matches_delta` (`abs_vs_unfoldable`;
  `bug-reports/closed/Bug2002`). **There is no eta rule**: `fun (x:a) -> f
  x` is not equal to `f`, whose domain may be larger than `a` (see
  `FStar.FunctionalExtensionality` and
  `tests/micro-benchmarks/Test.FunctionalExtensionality`).
* `match` against `match`: equal scrutinees and patterns, and branches
  related under the equation of the scrutinee with the pattern.
* Applications with the same head and arity: when they cannot be related
  without a guard, relating the arguments and relating the unfoldings are
  each sufficient but neither necessary, so Core emits their disjunction
  (`either_guard`). With `natlt n = i:nat{i < n}`, `natlt i <: natlt n`
  gives `(x < i ==> x < n) \/ i == n` (#4239). Exceptions:
  * arguments that are, or contain, abstractions, arrows or refinements
    (`args_contain_binders`) are related first, and the unfoldings only if
    that fails: the SMT encoding keys such binders on their free variables,
    so an equation between the whole terms is seldom provable;
  * in subtyping, e.g. `st pre post <: st pre' post'`, the unfoldings are
    related by implications;
  * heads marked `[@@unifier_hint_injective]` (e.g. LowParse's `parser k
    t`), as in Rel (`bug-reports/closed/Phase2CoreKindByEval`);
  * a quantifier-free guard of the unfoldings is taken on its own rather
    than in a disjunction, on which Z3 would case-split.
* Otherwise, one or both sides are unfolded (`maybe_relate_after_unfolding`)
  and the relation is retried. When nothing unfolds, the `fallback` emits
  an equation (or implication) between the terms, if a guard is allowed and
  the types are `equatable`.

**Unfolding.** An abstraction or a refinement is encoded as a fresh symbol
keyed on its free variables, so two such terms are provably equal only when
they are syntactically equal, and lemmas fire on the terms as written.
Core therefore chooses the form of a guard:

* When the unfoldings of two applications never come to have the same
  head, the guard is stated on the terms as they were, so that the SMT
  patterns of lemmas about them fire; likewise when one side is a variable
  (`examples/metatheory/StlcCbvDbParSubst`).
* Unfolding that reaches a `match` or a `fun` on one side while the other
  is still an application gives a guard on the folded terms, unless that
  application has no definition (e.g. `p ** q`).
* Unfolding that reaches a refinement is kept only if the refinement's
  base comes to have the same head as the other side, e.g. `nat` against
  `int` (`bug-reports/closed/Phase2CoreBranchTypeByUnfolding`,
  `Phase2CoreFoldedRefinements`).
* A recursive head is unfolded (`unfold_rec_head`) only if that closes the
  relation without a guard (`closes_with_zeta`, e.g. against a variable,
  normalizing once to head normal form; `bug-reports/closed/Bug3207b`), or
  when relating it to a `match` (`unfold_to_match`). Unfolding it
  otherwise could loop (`bug-reports/closed/Bug606`).
* A `match` whose scrutinee only reduces after unfolding is evaluated
  (`reduce_match`, `UnfoldUntil delta_constant`), and the result is kept
  only if a branch is taken
  (`bug-reports/closed/Phase2CoreStuckMatchByEval`).
* When neither side unfolds and one of them is a literal, both sides are
  evaluated (`closes_by_evaluation`).

### 6.5 Non-recursive `let`

`check_let` has three steps:

1. **The definition** (`check_let_def`). Without an annotation, its type is
   synthesized, and its universe computed without checking it again
   (`quietly (universe_of_well_typed_term ...)`). With one, the definition
   is checked, and then the annotation is checked to be a type:
   * a pure, ghost or `Lemma` definition (by `lb.lbeff`) is checked against
     the annotation (`check_against_typ_synth`), so that its obligations
     are emitted under its own hypotheses: in `let f : t = (lemma (); f0)
     in e`, `f0` meets `t` under the lemma;
   * an effectful definition has its type synthesized and related to the
     annotation (`check_against_typ_by_subtyping`): the postcondition of an
     effectful computation is carried only by its synthesized type, e.g.
     `n >= 0` after `if n < 0 then fail ""`
     (`FStar.Tactics.V2.Derived.repeatn`).

   `lb.lbeff`, the effect of the whole `let`, bounds that of the
   definition; it only selects between two sound strategies. The
   annotation is checked after the definition so that the well-formedness
   conditions it shares with annotations inside the definition (e.g. `j <
   length a` for a local lemma about `index a j` whose body binds another
   one) are emitted in the scope of the definition's goals, rather than
   closed over the annotation's binders and then dropped from the body as
   guard-cache hits (hacl-pulse `Spec.GF128.Poly.bits_inj`).
2. **The body**, with `x` bound at `let_binder_sort`: the annotation, or
   else the synthesized type. When a type was also synthesized for an
   annotated `let`, its refinement is added to `x`'s type: the annotation
   may be one that elaboration inferred, lacking the definition's
   postcondition. The body is checked against the expected type, if any.
3. **Closing** (`close_let_guard`). For an effectful definition, the guard
   is quantified over `x`. For a pure or ghost one, see §7: the defining
   equation, the facts about the definition, a local SMT lemma, `let
   unfold`. Without an expected type, the result type is computed by
   `let_result_typ`:
   * pure definition: `x` is substituted into the body's type; if `x` does
     not occur in it but the body is effectful, the definition's refinement
     is kept as `r:t{exists x. phi x}` (e.g. a `_:unit{False}` from
     `admit ()` before an effectful body that relies on it);
   * effectful definition: `x` is closed existentially, over what the
     body's type says about it and, for a pure body, over the body itself,
     e.g. `let s = f x in C s y : r:t{exists s. r == C s y}`. A name that
     escapes the base type is an error.

**Local SMT lemmas.** `let f x : Lemma p [SMTPat t] = ... in e` makes the
quantified lemma available in `e` (`smt_lemma_as_forall`), as
`TcTerm.maybe_intro_smt_lemma` does.

**`let unfold x = e`** (`inline_let_vc`) substitutes `e` into the VC. So
does every pure `let` under `--no_smt`.

### 6.6 `let rec`

`check_letrec_types` checks the declared types of the nest.
`check_letrec_defs` checks each definition with the other names bound at
their types refined for termination (`Termination.guard_letrecs`), as in
TcTerm. The refined types are checked in the context of the nest, which
catches ill-typed `decreases` clauses; `Termination.guard_letrecs` uses
fresh universe variables for `precedes` and `===`, which Core solves when
it checks those types. An admitted termination check (`admit_termination`)
still gives the definitions the refined types. The formals are named as in
the definition. A recursive name escaping into the type of an inner `let
rec` is an error.

### 6.7 `match`

One rule, `check_match`, checks every `match` against its `returns t`
annotation (§5):

* **At the pattern.** Each branch is checked against `t` with the pattern
  substituted for the `as` binder, `t[p_i/x]`, as in `TcTerm.tc_eqn`
  (`bug-reports/closed/Phase2CoreReturnsAtPattern`). When `t` is a
  refinement by a `match` on the same scrutinee (up to `TEQ.eq_tm`), the
  branch is checked against the formula of its own branch (`at_pattern`,
  up to a renaming of the pattern variables, `pat_rename`): the first
  formula branch with the same pattern, skipping those whose patterns are
  identical to an earlier branch's; a variable pattern matches anything.
  This spares the SMT solver reducing the match.
* When the annotation asks for equality (its `use_eq` flag, as for `$:`),
  each branch's type is related to `t` by `EQUALITY`.
* A dependent annotation (mentioning the `as` binder) requires a pure
  scrutinee. `returns C` is checked as `returns (comp_result C)`, plus a
  check of the effect. A tactic handler on the annotation is rejected.
* **Without an annotation** (built by tactics, or by Pulse, e.g. its join of
  postconditions), the match is checked against the expected type (e.g.
  the formal it is passed to), else its residual type, else the type of
  its first branch, which must not mention the pattern's variables
  (`check_no_escape`).
* **Patterns.** The scrutinee's type is unrefined through any number of
  refinements and abbreviations (`normalize_refinement`) before it is
  compared with a pattern's type. `when` clauses are rejected (Error 236),
  as TcTerm rejects them.
* **Branch conditions** (`pattern_branch_condition`) use discriminators and
  projectors applied to the scrutinee with the parameters and indices of
  its type (`inductive_type_args`), e.g. `TEq? #a #b #c s`, rather than a
  `match` on `s`, about which the SMT solver knows much less. The
  arguments are found in the scrutinee's type only for an indexed type;
  otherwise the parameters are the pattern's dot terms (finding them means
  normalizing the type, which can be slow). For a nested pattern, the
  scrutinee is a projection (`pat_field_projection`), whose type is the
  projector's result type; only if the projector or its arguments cannot
  be found is it a single-branch `match`, of unknown type. A projection is
  only well-typed when the enclosing discriminator holds, and it is only
  used under it: e.g. `C? s /\ P (C?.f s)` is false when `C? s` is,
  whatever `C?.f s` means (its SMT encoding is total). A pattern variable that a dot term
  mentions is replaced by the corresponding projection of the scrutinee
  (`pattern_var_projections`). A `()` pattern, a variable, or the only
  constructor of a type (with sub-patterns without conditions) has no
  condition.
* **Hypotheses** (`branch_conditions`). The guard of a branch is `hyp ==>
  forall xs. sc == p ==> G`, where `hyp` conjoins the path condition (the
  negated conditions of the earlier branches) with the branch's own
  condition, and `xs` are the pattern variables. The equation is the last
  hypothesis, where tactics look it up.
* **Exhaustiveness.** Unless the patterns are syntactically exhaustive
  (`match_is_syntactically_exhaustive`: a variable, or all the constructors
  of the scrutinee's type), the negated path condition after the last
  branch is an obligation (`exhaustiveness_obligation`), labeled at the
  match. Branches after a variable pattern are still checked, as dead code,
  but contribute no facts.

### 6.8 Quotes

The antiquotations of a static quote are checked against `term`; the quote
is a `term`. A dynamic quote has effect `TAC`.

### 6.9 Tactics

Core trusts nothing a tactic produces. `synth_by_tactic #t tau` comes in
two cases, decided by `VCUtil.synth_proof_goal`, which TcTerm and Core
share:

* **Proofs.** When `t` is a proof goal, i.e. all its inhabitants are `()`
  (`squash p`, `u:unit{p}`, or a proposition such as `a == b`), the
  elaborator does not run the tactic (`TcTerm.tc_synth`): it leaves
  `synth_by_tactic #t tau` in the term. Core checks it as an application
  and adds the guard `with_tactic tau p`, as for `assert p by tau`: the
  tactic proves the goal Core computes, in Core's context, when the guard
  is discharged. Checking a result `()` against `squash p` instead would
  ask the SMT solver to prove what the tactic proved (e.g. nonlinear
  arithmetic in `FStar.UInt128`, `FStar.Math.Euclid`). The driver then
  erases these applications to `()` (§2). In a lax definition, neither
  Core nor these tactics run.
* **Other terms.** The elaborator runs the tactic (§5) and Core checks its
  result like any other term. Core rejects a `synth_by_tactic` left unrun
  at such a type ("This synthesis by a tactic was not run"): the library's
  declaration of `synth_by_tactic` (`Tot t`) would otherwise give a value
  of any type with no obligation.

For `e <: t by tac`, the tactic is checked to be a total `unit -> Tac unit`
(`check_ascription_tactic`, as `TcTerm.tc_tactic`), and the guard of
checking `e` against `t` is wrapped with it, even when trivial
(`with_ascription_tactic`), so that `e <: t by fail ""` fails.

## 7. Guards, facts and caches

### Facts

TcTerm binds every sub-computation to a name of its (refined) type, so what
that type says is in scope for everything after it. Core synthesizes the
type of an application as the head's result type, which says nothing about
the arguments. Core recovers the missing information as **facts**
(`Core.Base.facts`, `Core.Facts`):

* Facts are computed by `do_check` in the same pass as a term's type, from
  the facts of its subterms, and are cached with the type. They are lazy
  (`Thunk`), since most are never used. No term is traversed or checked
  again to compute them.
* `f_sub`: the facts about a term's subterms: an application's arguments;
  the definitions of the `let`s it is made of (with a pure definition
  substituted for its variable, and the facts mentioning the variable of
  an effectful one dropped); and its branches, each under the condition
  that its branch is taken. A branch's facts that do not mention its
  pattern variables are stated as `cond ==> facts`; the others as `forall
  xs. sc == p ==> facts`. The facts of the second argument of a
  short-circuit operator are stated under the first's condition.
* `f_term`: what a pure term's type says about it (`term_facts`), plus
  `f_sub`. A term checked against an expected type (a pushed `let` or
  `match`) gets its facts from that type, plus its `f_tail`, which stands
  in for what its unsynthesized type would have said: e.g. the `squash p`
  of `lemma ()` in a branch `(lemma0 (); lemma ())` checked against `unit`.
* `f_tail`: the `f_term` of the expression that a term's `let`s end with.
* The result type of an application of a top-level function contributes a
  fact only when it is syntactically a refinement or a squash. A name that
  unfolds to a refinement (e.g. `pos`) contributes none: the function's
  typing axiom already gives that fact, and repeating it at every use adds
  nonlinear hypotheses that derail the solver.
* Atomic terms contribute no facts, except a top-level name whose type is
  `squash p` (e.g. a lemma used as a value): its fact is `p`.

Facts are hypotheses of the guard at a refinement-subtyping witness
(`witness_guard`), at the subtyping of a dependent non-atomic argument
(`with_deps`), and when a pure `let` is closed.

### Closing a pure `let`

A pure `let x = e1 in e2` closes the body's guard `phi` as `facts ==>
forall x. e1 == x ==> phi` (`close_with_definition`; the equation is
oriented as TcTerm's, `TcUtil.mk_binder_eqn`, which is how it is shown in
the context of a failed goal), simplified as follows (`close_let_guard`):

* The defining equation is dropped when it is useless (`def_eq_useful`,
  the analogue of `TcUtil.should_return`): `x`'s type, or its result type,
  is unit-like, or the definition's head is irreducible.
* The quantifier is dropped when, in addition, `x` is not free in `phi`. A
  useful equation is kept even then: it may trigger an SMT pattern, e.g.
  `introduce forall x y. q x y with let p = (x, y) in ()`.
* When `x` is quantified, its type says what `e1`'s type says: only
  `f_sub` is added. Otherwise `f_term`, preceded, for an annotated `let`,
  by what the annotation says about `e1` (`type_facts`), as TcTerm assumes
  it.
* When the annotation was pushed into `e1`, no type was synthesized, so
  `f_tail` is added: e.g. `eliminate exists x. p x with lemma x`
  elaborates to `let _ : unit = (let x = .. in lemma x) in ..`, where only
  the type of `lemma x` says what it proves
  (`PulseCore.IndirectionTheoryActions.witness_exists`).

So for a pure definition, what it establishes beyond its annotation reaches
the body as facts plus the defining equation, while for an effectful one it
reaches the body through the binder's type (`let_binder_sort`), the only
place its postcondition lives.

### Shape of guards

* A vacuous quantifier over a *null* `unit` binder is dropped, as by
  `Env.close_guard` (`mk_forall_l_gen`), except over the binders of the
  definition itself. Named `unit` binders (e.g. of `calc` step thunks) are
  kept: the SMT encoding assumes each quantifier-free conjunct of a guard
  while proving the next (`ErrorReporting.split_goals`), so dropping them
  would put every earlier `calc` step into the context of every later one.
  Likewise, a proven conjunct that is not quantifier-free contributes its
  quantifier-free parts; a conjunct mentioning a definition whose body is
  quantified is not assumed (#4615), unless the query already assumes that
  same atom.
* `either_guard` drops the caches of both alternatives when it emits a
  disjunction: their entries would claim their own guards were emitted.
* The SMT encoding names a function literal after its body and type,
  including its residual type, and the unifier may copy a literal with
  different residual types. In a guard, refined residual types are
  weakened to their unrefined types (`unrefine_abs_residuals`), unless the
  body is ascribed a refinement type
  (`bug-reports/closed/Phase2CoreAscribedResidual`).
* Core simplifies (`VCUtil.simplify_vc`) the guard of a refinement of
  `unit` it witnesses, e.g. `()` against `squash p`, as TcTerm did when
  creating it. This head-unfolds `unfold` abbreviations, e.g. `normal p`
  into the `norm [...] p` request it stands for, on which a tactic that
  processes the VC may depend (`OPLSS2021.ValeVCNoProp`).
* The guards returned by `check_term`, `check_term_at_type` and
  `compute_term_type` are simplified with `simplify_steps`.

### Caches

* **Term cache.** Every check memoizes `g |- e : E t` (with its facts); a
  later check of `e` in an extension of `g` is a hit.
* **Guard cache.** Every guard emitted is cached with its context; a guard
  found in the cache whose context is included in the current one is
  treated as already emitted (`guard`).
* **Two levels.** A computation adds its entries to the functional cache it
  threads (`cache_t`), which is valid only if its guard is. Once the caller
  has proven the guard, the entries are committed to the global cache with
  a token (`mk_token`, `commit_guard_core`; the `guard_and_tok_t` the API
  returns). The global cache is cleared by `clear_memo_table`: at each
  top-level declaration and around every elaboration (`Tc.elaborating`,
  `CoreCheck.elaborate`), since Core may run on unproven terms there.
* **Re-emitting.** A caller that transforms the guard of a sub-computation
  (closing, weakening, labeling, adding facts) must emit the result with
  `reemit_guard`, not `guard`: when the transformation is trivial, the
  entry found would be the one the sub-computation just inserted, and the
  guard would be silently dropped, which is unsound.
* **`quietly`** drops the guard of a computation whose guards have already
  been emitted (e.g. a universe of a type Core computed), and keeps its
  cache only when it had no guard. `type_of_for_hypothesis` similarly drops
  the guard of typing a term only used in a hypothesis that holds anyway,
  e.g. `e0 == p` on the branch where the scrutinee `e0` matches `p`, when
  relating two matches.
* **Relation failures.** Failures to decide a relation without a guard are
  remembered for the rest of a top-level check
  (`with_relation_failure_memo`), keyed on the relation, the terms, the
  (physical) environment and the flags; without it, a chain of failed
  unfoldings is retried from every level above it, which is exponential in
  its length. Returning a remembered failure is always sound.
* **Binder names.** Core names the binders it opens deterministically, so
  that its checks can be memoized. The indices start at 2^40
  (`core_index_base`), so that they never collide with names `GenSym`
  produces, e.g. for the local binders of a constructor's arguments
  (`tests/bug-reports/closed/Phase2CoreBinderNames`).

## 8. Error reporting

Core labels its guard so that a failed goal is reported with a useful
message, range and context, mostly as TcTerm's own guards were:

* the subtyping of a term at a type is labeled "Subtyping check failed" at
  the term, with "Expected type ... got type ...", except for a value of
  type `unit` given for a `squash p`, e.g. `()` for a precondition, which
  only locates the goal (`label_subtyping`);
* the body of a function checked against an arrow is located at the body,
  with "Could not prove post-condition" (`label_postcondition`); each
  binder's annotation with "Type annotation on parameter incompatible with
  the expected type";
* the obligations of a formal type, e.g. the termination refinement of a
  recursive call, are located at the argument;
* the exhaustiveness obligation is labeled at the match;
* the refinement of the domain of an arrow is a hypothesis of the guard of
  its codomain, not the sort of its quantifier;
* a failure to relate two applications reports the disjunction of
  `either_guard`;
* the failed annotation of a pattern binder is a subtyping failure at the
  binder; the obligation of a `calc` step's proof is located at the step.

The innermost label wins (`ErrorReporting.split_goals`). Pulse calls Core
directly, so these labels also show in Pulse's errors: an argument that
does not have its formal's type is "Subtyping check failed" at the
argument, and a termination obligation is at the decreasing argument.

## 9. What `.checked` files record

A client of a module sees the module's sigelts. For an unannotated
definition, that includes **the type recorded in `lbtyp`**. Unification in
a client compares the heads of the indices of that type, e.g. `raw a
(U32.add l1 l2)` against `raw a (l1 + l2)` ("head mismatch" in `Rel`). So
the recorded type must be stable, not merely equivalent to some other valid
type; otherwise dependents fail with elaboration errors (Error 54 or 189)
far from the change.

This is why Core checks against the type elaboration inferred (§2), and
that is the type recorded. Core's own inferred types (`--ext core_infer`)
differ in hundreds of places over `ulib`: abbreviations unfolded (`u32`
becomes `U32.t`), refinements typed as `eqtype`, `unfold` operators not
normalized.

Tests run with `--cache_off` elaborate their dependencies from source in
lax mode, so they cannot catch this class of problem. Build real `.checked`
files to test changes that affect recorded types.

The recorded terms are the elaboration, which is also what tactics inspect
and what is printed: every non-empty `match` carries its `returns`
annotation.

## 10. Known limitations and open questions

* **Not handled.** `when` clauses (Error 236), and `match ... returns`
  annotations with tactic handlers.
* **Synthesis outside `let`.** Only the definitions of top-level `let`s are
  elaborated with synthesis (`Tc.tc_sig_let`). A `synth_by_tactic` at a
  type that is not a proof goal elsewhere, e.g. in the type of a `val` or
  `assume val`, or of a constructor's argument, is not run, and Core
  rejects it.
* **Effectful binder strengthening.** For an annotated effectful `let`
  definition, the synthesized type refines the binder (`let_binder_sort`),
  because the postcondition of an effectful computation lives only in its
  type. Pure definitions instead pass what they establish beyond their
  annotation as facts with the defining equation (§7). Replacing binder
  strengthening for effectful definitions with facts about the bound result
  is open; it must preserve the postconditions the `let` exports in its
  result type when a pure definition precedes an effectful body, and local
  SMT lemmas (`smt_lemma_as_forall`).
* **Brittle proofs.** The quantifiers Core keeps or drops in a guard change
  the context of each goal (§7, `split_goals`), so a proof close to its
  rlimit may be sensitive to small changes in the shape of the VC.
* **Not entirely independent of TcTerm.** A few `Env` callbacks used by
  shared modules dispatch to TcTerm at runtime (§1).

## 11. Debugging

* `--debug Elab` prints the elaboration of each definition, the expected
  type given to Core, and the guard the driver discharges.
* `--debug CoreTop` prints each top-level query and its simplified guard,
  and warns about names free in the guard.
* `--debug Core` traces the checker; `CoreEq` traces its equality checks
  and cache statistics, and `CoreExit` its results.
* `--debug CoreFacts` shows the facts collected at each witness and `let`.
* `--debug DisableCoreCache` turns memoization off. Use it to rule out
  cache bugs.
* To tell an elaboration problem from a Core problem, check the module with
  `--admit_smt_queries true`: that only elaborates.
* `--log_queries` to compare the VCs Core sends before and after a change;
  identical `.smt2` files mean the change did not affect verification.

## 12. Performance

Most of the time spent checking a module goes to the SMT solver. Core's
memoization (§7) keeps its own cost low despite the facts it collects.

When comparing timings across a change, beware of the state of the
long-lived z3 process: F\* reuses one z3 process for a whole module, so
perturbing earlier queries changes how long later ones take, sometimes by
an order of magnitude for an identical query. Use `--z3refresh` (a fresh z3
for every query) to compare the time of individual queries.

Real slowdowns arise where a VC is split differently into goals, e.g. fewer,
larger goals (`ErrorReporting.split_goals`).
