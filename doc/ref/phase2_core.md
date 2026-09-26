# Phase 2 with Core (`--ext phase2_core`)

*A reference for F\* compiler developers.*

A top-level `let` is checked in two phases (`Tc.tc_sig_let`):

1. **Phase 1, elaboration.** `TcTerm` runs with `phase1 = true; admit = true`.
   It infers implicit arguments, universes and types, and inserts coercions.
   The result is a fully elaborated term that carries no unification
   variables.
2. **Phase 2, checking.** Without the extension, TcTerm runs *again* on the
   elaborated term, now producing verification conditions.

Under `--ext phase2_core`, phase 2 does not re-run TcTerm. It calls
`FStarC.TypeChecker.Core` on the phase-1 elaboration instead. Core is a
checker, not an elaborator. It does no unification and no inference of
implicits. It is also self-contained, which makes it a small, auditable
basis for a more trustworthy core of F\*. The extension builds on the
simplified effect system (see [simplified_effect_system.md](simplified_effect_system.md)).
Because `Tot`, `GTot` and `Div` are primitive, and specifications live in
refinements rather than in WPs, Core only has to know about four "effects":
`Tot`, `Ghost`, and an opaque *effectful* `M`.

Contents:

1. [Enabling it](#1-enabling-it)
2. [The driver](#2-the-driver)
3. [What Core had to learn](#3-what-core-had-to-learn)
4. [Guards and facts](#4-guards-and-facts)
5. [What `.checked` files record](#5-what-checked-files-record)
6. [Known limitations](#6-known-limitations)
7. [Debugging](#7-debugging)
8. [Performance](#8-performance)

---

## 1. Enabling it

The mode is taken from `--ext phase2_core=<mode>`. If that is not given, it
comes from the environment variable `FSTAR_PHASE2_CORE`, which is convenient
for whole builds, e.g. `FSTAR_PHASE2_CORE=strict make ci`. See
`TcUtil.phase2_core_mode`.

| mode                   | behaviour |
|------------------------|-----------|
| unset, `0`, `false`, `off` | Phase 2 is TcTerm, as before. |
| `warn`                 | Diagnostic. Core runs. If Core fails, either structurally or because its guard cannot be proved, the failure is reported as Warning 290 (`Warning_Defensive`) and TcTerm's phase 2 runs instead. |
| `compare`              | Diagnostic. Core runs, and then TcTerm's phase 2 always runs and its result is used. Warning 290 is reported whenever the two record different types (`lbtyp`) for a definition (see §5). Core failures are reported as in `warn` mode. |
| anything else, e.g. `strict` | Core's result is used. See §2 for failures. |

The extension is skipped for any definition checked with `admit` set
(`--admit_smt_queries`, lax mode, and so on). It is also skipped when the
module is not checked in two phases.

## 2. The driver

The driver is `Tc.tc_sig_let`, together with `Tc.tc_sig_let_phase2_core`.

* **Non-recursive `let`.** The elaborated definition is checked with
  `Core.compute_term_comp` against an expected type:
  * the user's annotation, if there is one;
  * otherwise, **the type phase 1 inferred**. `drop_lbtyp` erases that type
    from the term, so that TcTerm's phase 2 re-infers it, but the driver
    remembers it.

  Core does no inference, even at the top level. The phase-1 type is the one
  TcTerm's phase 2 would record, which matters to clients (§5). This type is
  not checked for well-formedness (`check_t = false`). It may only be
  well-formed in the context the definition sets up. For example, for
  `let n = f b in lem b; U32.uint_to_t n` the type is `x:U32.t{v x = f b}`,
  where `=` is taken at `uint_t 32`; TcTerm does not check it either. The
  old behaviour, in which Core infers the type, is still available with
  `--ext phase2_core_infer`.

  In that mode, the inferred computation type is normalized as TcTerm's
  `check_expected_effect` would normalize it (`Beta; Eager_unfolding;
  NoFullNorm; Exclude Zeta`). Only the result of the arrow is normalized; its
  binders are left as written.

  The definition is then finished by `TcTerm.finish_top_level_let`, which is
  factored out of `check_top_level_let`. It masks top-level effects, checks
  that the type is inhabited, applies tcnorm, and closes the universes.
  Core's guard is discharged there, with the user's annotation, not the
  phase-1 type, as `topt`.
* **Recursive `let`s.** These use `Core.check_top_level_letrec`. The
  recursive names are replaced by fresh variables. Their types are refined
  for termination using `TcTerm.guard_letrecs`, exactly as TcTerm does, and
  the nest is checked like an inner `let rec`.
* **Failure in strict mode.** Only Core decides whether a definition is
  accepted, and Core reports why it is not. TcTerm's phase 2 is not run to
  explain a rejection, which would double the work on every failure.
  * An unprovable guard is reported by the SMT solver, as for TcTerm, with
    the labels and ranges Core puts on the guard (§6, "Error reporting").
  * A structural failure is reported with Core's error. Where TcTerm has an
    error code for the same failure, Core's error carries it
    (`Core.error_code`) and is reported with it, and with TcTerm's message:
    Error 34 for a computation of the wrong effect (e.g. `GTot` for `Tot`),
    Error 236 for a `when` clause. Any other structural failure is Error 12,
    "Core failed to check this definition", followed by Core's context. It
    is located at the innermost term of that context (`Core.error_range`).
* **Ill-scoped phase-1 terms.** Lax phase 1 can leave a free name in its
  elaboration. For example, a uvar standing for the residual type of an
  abstraction, whose context includes a `let`-bound name, may be solved
  after that `let` is closed. TcTerm's phase 2 never sees this, because it
  re-elaborates. If the phase-1 term has free names, the driver uses TcTerm
  for that definition, in every mode (`--debug TwoPhases` reports it).

Phase 1 behaves differently in one respect. In `TcTerm.check_inner_let`,
phase 1 normally erases the inferred type of every unannotated *inner* `let`,
so that phase 2 can infer it again. Under the extension, the inferred type is
kept, because Core needs a type on every binder.

**Monadic annotations must be right in phase 1.** Under the extension,
nothing re-elaborates the phase-1 term, so its `Meta_monadic`,
`Meta_monadic_lift` and `lbeff` annotations are what extraction and
reification see. TcTerm's own phase 2 re-derives them in `check_inner_let`: the
definition is lifted to the effect of the whole `let`, which is also its
`lbeff`. Two let-insertions in TcTerm did not follow that rule and were fixed
(the fix applies with or without the extension):
* `tc_match`, for an impure scrutinee: `let x = e in match x with ...` now
  lifts `e` to the effect of the match, and uses that effect as `lbeff`.
  Previously, a `Dv` scrutinee in `Tac` code was extracted as reified `TAC`.
* `tc_app`, when binding effectful arguments (`bind_lifted_args`): `lbeff`
  and `Meta_monadic` now use the effect of the application, not of the
  argument. Previously, reifying such an application failed.

**Tactics that produce terms run in phase 1.** `synth_by_tactic` and the
tactic of an ascription `e <: t by tac` are run in phase 1 under the
extension (`TcUtil.synth_in_phase1`), and their results are left in the
elaborated term, since nothing else would run them.

**Projector types of parameterized inductives** (`TcInductive`, applies with
or without the extension). A projector's type substitutes the earlier fields
of the constructor by projections of the projectee. Those projections were
built without the type's parameters, i.e. as ill-typed terms that TcTerm's
Rel tolerated but Core rejects. They now take the parameters as implicit
arguments.

**Guards are simplified before discharge.** TcTerm simplifies guards as it
builds them, without full normalization (`TcUtil`). The driver does the same
to Core's guard (`Rel.simplify_guard`) before discharging it. It matters for
normalization requests: in `norm [nbe; primops] ("a" ^ "b") == "ab"`, the
simplifier reduces the argument's primitive application first, whereas
processing the request itself, with only `primops`, does not unfold `(^)`.

TcTerm also simplifies each precondition as it creates it, i.e. the guard of
`()` against `squash p` (`value_check_expected_typ`, via
`TcUtil.simplify_and_label_guard`). This head-unfolds `unfold` abbreviations,
e.g. `normal p` into the `norm [...] p` request it stands for, and a tactic
that processes the VC may depend on it (`OPLSS2021.ValeVCNoProp`). Core does
the same (`Rel.simplify_vc`) when it witnesses a refinement of `unit`.

## 3. What Core had to learn

Core previously served tactics (`core_check`) and only knew `Tot` and
`GTot`. For phase 2 it had to accept everything the elaborator produces:

* **Effects.** `tot_or_ghost` became `eff = ETot | EGhost | EEff of lid`, with
  `join_eff` and `sub_eff`. An effectful computation, such as `Dv`, `ST` or a
  user effect, is opaque, and its result is a binder, never a term:
  * it is never substituted into a type;
  * an effectful `let` closes its variable existentially in the result type,
    as `TcUtil` does;
  * an effectful argument on which the type of the application depends is
    rejected;
  * as in `N.ghost_to_pure2`, `GTot` is promoted to `Tot` when it is lifted
    to, or composed with, an erasable effect, which already accounts for
    its erasability (e.g. `let f () : MGhost int = f_ghost_info () + 2` in
    `micro-benchmarks/Erasable`).
* **Checking mode.** `check_against_typ` and `check_against_comp` push an
  expected type into `let`s, `match`es and `fun`s, as TcTerm does. Guards are
  then emitted where the relevant binders, path conditions and local lemmas
  are in scope.
  * A `fun` checked against an arrow has its body checked against the
    arrow's computation type (`abs_against_arrow`). It is not synthesized
    and then subtyped.
  * The arrow may be behind an abbreviation. Its unfolding may be ascribed,
    e.g. `let act a = f:slprop -> action a f <: Type`, and the ascription is
    ignored.
  * A `fun` may have more binders than the arrow, e.g. `fun frame s0 -> e`
    against `frame:slprop -> action a frame`, where `action a frame` is
    itself an abbreviation for an arrow. The first binders are then checked
    against the arrow, and the function of the rest against its result.
  * Refinements are never looked through for this, since that would drop
    their predicates.
  * The same applies to a `fun` passed as an argument whose formal type is
    an arrow, e.g. the proof in `introduce exists x. p x with w and (fun _
    -> ...)`.
  * An annotated `let` whose definition is a `let`, `match` or `fun` is
    checked against its annotation when the definition's own type needs a
    guard to be related to it. For example, in `let f : t = lemma (); f0 in
    e`, `f0`'s type is related to `t` under `lemma`'s postcondition.

  In each case the guard is proved in the same scope as the hypotheses of
  the body. The SMT solver uses what it learns proving one conjunct to prove
  the next, so separating the two can make a proof fail.
* **Top-level APIs.** `check_term_at_comp`, `compute_term_comp` and
  `check_top_level_letrec`.
* **`let rec`**, both inner and top-level, with termination as described in
  §2.
* **Local SMT lemmas.** `let f x : Lemma p [SMTPat t] = ... in e` makes the
  quantified lemma available in `e` (`smt_lemma_as_forall`), as
  `TcTerm.maybe_intro_smt_lemma` does.
* **`match`.**
  * Branch conditions are expressed with projectors and discriminators, so
    they do not mention the pattern variables. Both are applied to the
    scrutinee with their implicit arguments, the parameters *and indices* of
    the scrutinee's type (`inductive_type_args`), as `TEq? #a #b #c s`
    rather than as a `match` on `s`: the SMT solver knows much less about a
    `match` term, e.g. when the scrutinee is itself a projection, as in the
    exhaustiveness condition `TEq? b && Nat? (TEq?.t b)`. This is done only
    for an indexed type. For any other type, and when the type is not
    found, the parameters are the pattern's dot terms. Looking up the
    scrutinee's type means normalizing it, which for a large
    non-indexed type (e.g. the connectives of `FStar.Classical.Sugar`)
    was very slow for nothing.
  * A pattern variable that a dot term of the pattern mentions is replaced,
    in the branch condition, by the corresponding projection of the
    scrutinee (`pattern_var_projections`).
  * A `()` pattern has no branch condition, as in TcTerm.
  * The branch hypotheses (path condition, branch condition, equation
    between the scrutinee and the pattern) are separate implications, in
    that order, as tactics that address hypotheses by position expect.
  * `when` clauses are rejected (a structural failure), as TcTerm rejects
    them in verify mode; strict mode then reports TcTerm's error.
  * `match ... returns C` is checked like `returns t`, where `t` is `C`'s
    result type, plus a check of the effect. That covers effectful
    annotations such as `returns St t`, since computation types carry no
    other specification.
  * The type of an unannotated effectful match is refined with what each
    branch's type says under that branch's condition, as in
    `TcUtil.bind_cases`. A pure branch also contributes the equation between
    the result and the branch. Facts that mention the pattern variables are
    quantified existentially, together with the equation between the
    scrutinee and the pattern, e.g., `PH? h ==> (exists p. h == PH p /\ r ==
    p)`.
  * The discriminators in branch conditions keep the constructor's dot
    patterns, so they are well-typed when Core meets them again in a type.
  * The scrutinee's type is unrefined through any number of refinements and
    abbreviations before it is compared with a pattern's type.
  * Exhaustiveness is checked with the negated path condition.
* **Effectful `let`.** An effectful `let x = e1 in v`, where `v` is pure and
  does not mention `x`, has the type `r:t{r == v}`. When `v` mentions `x`,
  the equation is closed existentially over `x`.
* **Nested `Tm_meta`.** An expected type is pushed through any stack of
  `Tm_meta` nodes (e.g. `Meta_desugared Sequence` over `Meta_monadic`) to the
  `let` or `match` underneath.
* **Refinements** are typed `Type u`, even when their sort is an `eqtype`, as
  TcTerm types them.
* **`let unfold x = e`** (`inline_let_vc`) substitutes `e` into the VC. So
  does every pure `let` under `--no_smt`, so that the guard may simplify to
  `True` when it relates `x` to its definition.
* **A refinement lost to an effectful body.** In `let x = e1 in e2` with
  `e1` pure and `e2` effectful, what `x`'s type says is kept in the type of
  the `let` (`r:t{exists x. phi x}`) when `x` does not occur in `e2`'s type,
  e.g. for `let Some y = admit (); f () in ...` with `admit () :
  _:unit{False}`: the exhaustiveness condition of the pattern needs it.
* **`reflect`.** `M.reflect e`, checked against a computation type in `M`,
  checks `e` against the reification of that computation type.
* **Quantifiers without universes.** `l_Forall`/`l_Exists` as the
  desugarer produces them, without universe instantiations, get the
  universe of their domain, and relate to their instantiated forms.
* **Equality ascriptions** `e $: t` check `e`, then relate its type to `t`
  by `EQUALITY`.
* **Ghost to total promotion.** A ghost computation checked against a
  non-informative type counts as total, as in TcTerm.
* **`let rec`**: an admitted termination check (`admit_termination`) still
  gives the other definitions the refined types; the `<<`-refined types are
  checked in the context of the nest, which catches ill-typed `decreases`
  clauses in polymorphic recursion.
* **Eta.** `fun x -> e` relates to a non-abstraction `t` by relating `e` to
  `t x` under the binder, in both directions.
* **Unfolding.** As in Rel, when the delta-unfoldings of two applications
  never come to have the same head, the guard is stated on the terms as
  they were, not on their unfoldings; otherwise the SMT patterns of lemmas
  about them do not fire (e.g. `denote_term (elab_exp (open_exp e x)) ==
  open_term_spec' (denote_term (elab_exp e)) x`, where `open_term_spec'`
  unfolds to another recursive function). The same holds when one side is
  a variable: the index `g'` of a pattern-bound `h:typing g' e t` is
  related to `extend_gen x t g` by `g' == extend_gen x t g`, which the SMT
  solver proves by inverting `h`'s type, and not to the `match` that
  `extend_gen` unfolds to, whose λ it cannot equate
  (`examples/metatheory/StlcCbvDbParSubst`). A recursive definition is
  unfolded (with `Zeta`, when a guard is allowed) only if the unfolding
  closes the relation without a guard, e.g. by reducing by iota.
* **Equations between applications.** When two applications with the same
  head cannot be related without a guard, two guards are possible: one
  relating the arguments, and one relating the unfoldings, or (for an
  equatable head) the whole equation. Each is sufficient but neither is
  necessary. For example, `seq_seq_match p c s 0 n == seq_seq_match p c s'
  0 n'` holds if `s == s'` and `n == n'` by a lemma, while `on_domain a
  (fun _ -> False) == on_domain a p` may only be a hypothesis. Core emits the
  disjunction of the two guards (`either_guard`).
  * The exception is an *equation* whose corresponding arguments are
    abstractions, e.g. `forevery (fun i -> p i) == forevery (fun i -> q i)`.
    There the arguments are related first, and the unfoldings only if that
    fails. The unfoldings would just relate the same abstractions again,
    one level deeper, so a disjunction would repeat the argument-wise
    guard at every level of nesting. That was enough to make an easy SMT
    query time out.
  * This does not apply to subtyping, e.g. `st pre post <: st pre' post'`:
    the unfoldings are related by implications, while the arguments could
    only be related by equations.
* **Terms synthesized by tactics.** Phase 1 runs the synthesis, since
  nothing re-elaborates its output. A goal may still mention unification
  variables that are solved only after the tactic would have run: in
  `conv_squash h (_ by trefl ())`, the implicits of `conv_squash` wait on
  the deferred subtyping of `h`. So a definition that mentions
  `synth_by_tactic` is elaborated twice by phase 1: first without
  synthesis, and then with it, over the first elaboration, whose goals are
  fully resolved, as in TcTerm's phase 2.

  TcTerm trusts the result of `_ by tac`: it gives it the
  requested type without checking it. Checking the result again, e.g. `()`
  against `squash goal`, would ask the SMT solver to prove the goal the
  tactic proved, which may be well beyond it (nonlinear arithmetic in
  `FStar.UInt128` and `FStar.Math.Euclid`). Under phase 1, `tc_synth`
  therefore marks its result as `Tm_meta (Tm_ascribed (e, typ),
  Meta_desugared Tactic_synthesized)`. Core only checks that `typ` is a
  type and returns `typ`. The trust is the same as TcTerm's, but it is now
  explicit and confined to that one node. TcTerm, when it is phase 2 (e.g. in `warn` mode),
  trusts it too. The normalizer keeps the marker, as it does
  `Machine_integer`. The marker contributes no facts. It only lives while
  Core checks the definition: the driver removes it
  (`Tc.strip_tactic_synthesized`) before the definition is recorded, so
  clients and tactics (e.g. `def_of` in
  `examples/tactics/Normalization.fst`) see the tactic's result as TcTerm
  records it.
* **Unification inside Core.** `Rel.teq_nosmt_force` may raise, e.g. on an
  unsatisfiable universe constraint, rather than return false. Core wraps it
  so that such a failure is just a failed comparison.
* **Elaboration inside Core.** Core occasionally elaborates a term with
  TcTerm, e.g. the `<<`-refined types of the recursive bindings of a `let
  rec`. The guards of such elaborations must not be discharged in
  `g.tcenv`: that environment lacks Core's hypotheses (the equations of the
  enclosing `let`s and the facts), so they are checked with `admit`. The
  types involved are already known to be well-formed.

## 4. Guards and facts

TcTerm binds every sub-computation to a name of its (refined) type, so what
that type says is in scope for everything after it. Core synthesizes the type
of an application as the head's result type, and that type says nothing
about the arguments. Core instead recovers the missing information as
**facts**:

* `term_facts g a` is what the (memoized) type of the pure term `a`, and
  recursively those of its subterms, say about `a`.
* `app_facts` collects the facts of an application's arguments, of the
  definitions of the `let`s it is made of, and of its branches, each under
  the condition that its branch is taken.
* Facts are added as hypotheses:
  * of the guard at a refinement-subtyping witness (`witness_guard`);
  * of the subtyping of an argument whose formal type depends on earlier
    arguments (`deps` in `check_app_arg`);
  * when a pure `let` is closed.
* The result type of an application of a top-level function contributes a
  fact only when it is syntactically a refinement or a squash, e.g.
  `c:U64.t{v a >= v b ==> v c = pow2 64 - 1}` for `U64.gte_mask a b`
  (which `FStar.UInt128.gte_mask` needs). It contributes none when it is
  a name that unfolds to a refinement, e.g. `pos` for `pow2 n`. The
  function's typing axiom gives the SMT solver such a fact, as with TcTerm,
  and stating it at every use only adds hypotheses about nonlinear terms.
  These made `FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1` and
  `division_multiplication_lemma` fail with some z3 seeds.
* Atomic terms (names, constants) contribute no facts. Their types are
  already assumed by the SMT encoding. The exception is a top-level name
  whose type is a squashed proposition `squash p`, such as a lemma
  instantiated as a value (`let _ = lemma_name in ...`): its fact is `p`.
* A branch's facts that do not mention its pattern variables are stated as
  `cond ==> facts`, where `cond` is the path and branch condition, rather
  than under a quantifier over the pattern variables. The SMT solver can
  then use them without instantiating a quantifier (as `eliminate exists`
  requires).

A pure `let x = e1 in e2` closes its guard as `forall x. x == e1 ==> facts ==>
phi`. Several cases are simplified:
* The defining equation is dropped when it is useless (`def_eq_useful`, the
  analogue of `TcUtil.should_return`): the type of `x` is unit-like, or the
  head of `e1` is irreducible.
* The quantifier is dropped when, in addition, `x` is not free in `phi`. A
  useful equation is kept even when `x` is not free in `phi`: it may be what
  triggers an SMT pattern, as in `introduce forall x y. q x y with let p =
  (x, y) in ()`.
* Only the facts about the subterms of `e1` are added when `x` is already
  quantified at its own type, whether or not with its defining equation.
  What `x`'s type says about `e1` is then redundant, and, stated about `e1`
  with no equation relating it to `x`, only adds a quantified hypothesis
  that the SMT solver may trip on (`eliminate exists` with many binders,
  whose `indefinite_descriptionN` heads are irreducible).
* A vacuous quantifier over a *null* binder of type `unit` is dropped when
  the guard is closed, as by `Env.close_guard`. Named `unit` binders, e.g.
  those of the thunks `fun () -> ...` a `calc` elaborates to, are kept.
  The SMT encoding assumes each quantifier-free conjunct of a guard while
  proving the next (`ErrorReporting.split_goals`). Dropping these
  quantifiers therefore put every earlier `calc` step into the context of
  every later one. With nonlinear steps that derailed the solver, e.g. 3.8s
  instead of 0.2s for a step of `FStar.Math.Fermat.pow_plus`.
* The driver opens the leading quantifiers of a top-level guard, e.g.
  over the binders of `let f x y = ...`, into the environment in which it
  discharges the guard (`open_foralls` in `Tc.fst`). TcTerm discharges
  such a guard with the binders in the environment, so a
  `handle_smt_goals` tactic sees `False` rather than `forall (_:unit).
  False` (`examples/tactics/HandleSmtGoal`), and the context of a failed
  goal is the same. For this, the null `unit` binder of `let f () = ...`
  is kept (`at_top` in Core's environment).
* When `x` is not quantified and the `let` is annotated, what the
  annotation says about `e1` is added as a fact, before `e1`'s own facts.
  The two may be `term_eq` and still differ: `term_eq` ignores the residual
  types of abstractions, but the SMT encoding of an abstraction depends on
  them. TcTerm assumes the annotated form.

This is the first of the hoped-for benefits. Equalities and postconditions
reach the VC without every intermediate term being named in the refinements
of bound variables.

**The guard cache.** Core memoizes both types and guards. A guard found in
the cache whose context includes the current one is treated as already
emitted. A caller that transforms the guard of a sub-computation, by closing,
weakening or adding facts, must re-emit it with `reemit_guard` rather than
`guard`. Otherwise, when the transformation is trivial (for example, closing
over no binders), the cache hit on the entry the sub-computation just
inserted silently drops the guard. That was an unsoundness.
`quietly` drops the guard of a computation that has already been checked,
but keeps the cache only when there was no guard.

## 5. What `.checked` files record

A client of a module sees the module's sigelts. For an unannotated
definition, that includes **the type recorded in `lbtyp`**. Unification in a
client compares the heads of the indices of that type, e.g. `raw a (U32.add
l1 l2)` against `raw a (l1 + l2)` ("head mismatch" in `Rel`). So Core must
record *the same* type that TcTerm records, not merely an equivalent one.
Otherwise dependents fail with phase-1 errors (Error 54 or 189) far from the
change.

This is why phase 2 checks against the phase-1 type (§2). An earlier
approach recorded Core's own inferred types. `compare` mode over `ulib`
found about 500 differences:
* abbreviations unfolded (`u32` became `U32.t`, `a ^-> b` became
  `restricted_t a (fun _ -> b)`);
* refinements typed as `eqtype`;
* unnormalized `unfold` operators.

With phase-1 types, about 30 differences remain. In these, TcTerm's phase 2
adds refinements that lax phase 1 omits:
* the postcondition of a lemma called in the body;
* the per-branch refinements of a `match`.

The definitions are transparent to SMT in every such case.

Tests run with `--cache_off` lax-check their dependencies from source, so
they cannot catch this class of problem. Use `compare` mode, or build real
`.checked` files under the flag.

## 6. Known limitations

* **Error reporting.** Core labels its guard as TcTerm labels its own, so
  that a failed goal is reported with the same message, at the same range,
  and in the same context:
  * the subtyping of a term at a type is labelled "Subtyping check failed"
    at the term, with "Expected type ... got type ...", except for a value
    of type `unit` given for a `squash p` (e.g. `()` for a precondition),
    which only locates the goal (`label_subtyping`, as
    `TcTerm.value_check_expected_typ`);
  * the body of a function checked against an arrow is labelled at the
    abstraction with the position-only "Could not prove post-condition"
    (`label_postcondition`, as `TcTerm.check_expected_effect`), and each
    binder's annotation with "Type annotation on parameter incompatible
    with the expected type" (as `TcTerm.tc_abs_check_binders`);
  * the obligations of a formal type, e.g. the termination refinement of
    a recursive call, are located at the argument; the formals of a
    recursive function are named as in its definition, not as in its type;
  * branch conditions are TcTerm's: the negation of the earlier patterns
    and the pattern's own condition, then the scrutinee's equation, last;
    the exhaustiveness obligation is labelled at the match;
  * the refinement of the domain of an arrow is a hypothesis of the guard
    of its codomain, not the sort of its quantifier.

  Some differences remain, because Core's VCs are deliberately not
  TcTerm's. The tests whose expected output shows them are pinned to
  TcTerm with `--ext phase2_core=off` (`tests/error-messages/Makefile`):
  * Core's VC carries more facts (§4), which then show in the context of a
    failed goal, e.g. the refinement of `bad (x-1)` in
    `NegativeTests.ShortCircuiting`, or the definition `f = fun n -> n` in
    `Coercions`. They may also prove what TcTerm cannot: in
    `TestErrorLocations.test_elim_exists`, the postcondition of
    `indefinite_description1` proves the assertion, and only the
    precondition fails;
  * Core relates two applications either by unfolding or argument-wise
    (`either_guard`), and a failure reports the disjunction
    (`Test.FunctionalExtensionality`);
  * the failed annotation of a pattern binder is a subtyping failure at
    the binder, not a failed assertion of the whole definition (`PatAnnot`);
  * the obligation of a `calc` step's proof is located at the step, not at
    its relation (`Calc`), because Core's post-condition label covers the
    whole body of the step's thunk, whereas TcTerm's covers only the final
    subsumption.
* **Not yet handled natively.** Core rejects the following, or checks them
  less precisely than TcTerm:
  * `when` clauses (rejected with TcTerm's Error 236, as TcTerm rejects
    them in verify mode);
  * `match ... returns` annotations with tactic handlers;
  * the SMT-pattern checks of `check_smt_pat`.
* **Elaborated terms differ.** Terms that tactics inspect are phase 1's
  elaboration, which lacks some of the ascriptions TcTerm's phase 2 adds
  (e.g. on a `match`, `TcTerm.tc_match`). `tests/tactics/DeltaDepth.fst`
  accepts both forms.
* **Brittle proofs.** A proof that TcTerm discharges close to its rlimit may
  flip, because the VCs are shaped differently. In particular, the SMT
  encoding proves each conjunct of a guard assuming the quantifier-free
  conjuncts before it (`ErrorReporting.split_goals`), so the quantifiers
  Core keeps or drops change the context of each goal (§4). The proofs
  changed were:
  * `FStar.Math.Lemmas.modulo_sub_lemma` got a hint. In `lemma_mod_plus`
    and `lemma_div_plus`, a linear `calc` step (`== {}`) is now proved by a
    private lemma, in an empty context. With the facts about `/` and `%`
    in scope, the step used nearly all of its rlimit in `strict` mode, and
    `lemma_div_plus` failed with z3 seed 7 in mode 0 too. The module now
    passes in both modes across z3 seeds 0, 1, 3, 7, 13 and 42;
  * in `FStar.Math.Fermat`, one step of `binomial_theorem` became the
    top-level lemma `binomial_theorem_ends`, its rlimit factor went from 4
    to 8, and `fermat_alt` got an explicit `pow` unfolding. The proof was
    brittle under TcTerm too: it failed in isolation under
    `--admit_except`. It now passes in both modes across z3 seeds.
  * `pulse/share/pulse/examples/Quicksort.Base.lemma_sorted_append`
    needed 13 attempts under `--retry 10` in mode 0 and never passed in
    strict mode: the SMT solver found the quantifier instances only by
    luck. It now instantiates them explicitly with `sorted_elim`,
    `larger_than_elim` and `smaller_than_elim`, and the `--retry` is gone.
    It passes on the first attempt in both modes across z3 seeds.
  * `examples/dsls/bool_refinement/BoolRefinement.rename_elab_binding_denote`
    failed at fuel 2 in both modes and needed fuel 4 or 8, near its rlimit,
    to push `subst_term_spec` through the nested `eq2` application. It now
    asserts that chain one level at a time and passes at fuel 2 with rlimit
    ~3 in both modes.
  * `FStar.UInt<N>.eq_mask` and `gte_mask` (generated from
    `.scripts/FStar.UIntN.fstip`) got `--z3rlimit 10`. Under TcTerm,
    `gte_mask` used 4.1 of its rlimit of 5 and failed with z3 seed 3; in
    `strict` mode it failed with seed 0 when checked with the
    implementation. It now uses at most ~5.5.
  * `tests/custard/CborBoundary.item` got `--z3rlimit 10`: its
    machine-integer bounds are proved under a dozen branch conditions, and
    used 4.7 of the default rlimit of 5 under TcTerm and ~5.6 under Core.
* **Tests changed.** Pulse checks its terms with Core in every mode, so the
  labels of §6 "Error reporting" show in the expected output of Pulse's
  failures (`pulse/test/Test.Recursion`, `nolib/Bug416`,
  `error_messages/{ReturnImplicit,SubtypingFailure}`,
  `bug-reports/{Bug59,Bug94,Bug100,Bug206}`): an argument that does not
  have its formal's type is reported as "Subtyping check failed" at the
  argument, with the expected and actual types, where it was "Assertion
  failed" at the application; a termination obligation is located at the
  decreasing argument.

  `pulse/test/bug-reports/Bug216.fst` expected Core, as
  Pulse uses it (`refl_tc_term`), to reject a `Tac` function argument such
  as `foo 1 (fun _ -> dump "")`, because Core only knew `Tot` and `GTot`.
  Since Core has learnt effects, those definitions are accepted in every
  mode, so the `expect_failure`s were removed.

  Tests whose expected output shows phase 2's elaboration are pinned to
  TcTerm with `--ext phase2_core=off` in their Makefiles. Phase 1's
  elaboration lacks TcTerm's result ascriptions on matches
  (`error-messages/TuplePat`, `ide/emacs/Fib.compute`, where `compute`
  gives `8` rather than `8 <: int`). It also creates fewer fresh names, and
  these outputs print their unique ids (`error-messages/Monoid`,
  `tactics/Postprocess`, `bug-reports/closed/Bug4274`). The ids in the last
  two also shifted in mode 0, because of the flag-independent fixes of §2,
  and their expected outputs were refreshed.

  Pulse calls Core directly, so Core's flag-independent changes show in
  the expected outputs of four Pulse tests in every mode, and those were
  refreshed. `pulse/test/bug-reports/Bug59` now reports the subtyping guard
  `has_type y a` (as `Rel.guard_of_prob` does) instead of `b == a`.
  `Bug100` and `Bug267` show `nat`'s refinement `i >= 0` rather than
  `b2t`'s unfolding `i >= 0 == true`. `ExistsErasedAndPureEqualities`
  prints different unique ids.
* **Ill-scoped phase-1 terms** still fall back to TcTerm's phase 2 (§2):
  this is the only fallback in strict mode.

## 7. Debugging

* `--debug CoreTop` prints each top-level query and its simplified guard.
* `--debug Core` traces the checker.
* `--debug CoreFacts` shows the facts collected at each witness and `let`.
* `--debug TwoPhases` prints the phase-1 elaboration, the expected type
  given to Core, and the guard the driver discharges.
* `--debug DisableCoreCache` turns memoization off. Use it to rule out cache
  bugs.
* `FSTAR_PHASE2_CORE=warn` on a module lists every definition Core cannot
  yet handle, without failing the build.
* `FSTAR_PHASE2_CORE=compare` additionally lists every definition whose
  recorded type differs from TcTerm's.

## 8. Performance

Measured on the 20 largest `ulib` modules, each checked from source with
`--cache_off` against the `stage2` library (stage-1 compiler, 16 checks at a
time on a 128-core machine). The total wall-clock time is 397s in mode 0 and
417s in `strict` mode (+5%). By module, the difference ranges from -6%
(`FStar.Math.Lemmas`, `FStar.Math.Pow`) to +27%
(`FStar.Reflection.TermSpec.Lemmas`). Peak memory is the same in both modes
(at most ~610MB).

Much of the difference is not in the VCs themselves but in the state of the
long-lived z3 process. F* reuses one z3 process for a whole module, so
perturbing the earlier queries changes how long later ones take. For example,
`FStar.Rational.m4` (a one-line nonlinear lemma) takes 0.18s in mode 0 and
1.58s in `strict` mode when the whole module is checked, but its logged query
is identical in both modes and takes 0.09s in each when checked alone. With
`--z3refresh` (a fresh z3 for every query), `strict` mode is slightly faster
than mode 0 on the modules that looked slowest:

| Module | default z3 (off / strict) | `--z3refresh` (off / strict) |
|---|---|---|
| `FStar.Rational` | 14.1s / 17.5s | 16.2s / 15.9s |
| `FStar.UInt128` | 46.1s / 54.0s | 62.7s / 60.8s |
| `FStar.Seq.Permutation` | 16.2s / 19.1s | 18.2s / 19.8s |

`FStar.Seq.Permutation` is the exception: its extra time is real and all in
`foldm_snoc_split'`. There, Core sends 43 larger goals where TcTerm sends 81
smaller ones, and the SMT time is 5.3s against 2.05s.

With `--admit_smt_queries true` the two modes take the same time on the
modules with the largest differences (within 3%). With `--profile`, Core's
phase 2 of `FStar.Reflection.TermSpec.Lemmas` takes 10.3s against 9.8s for
TcTerm's. So memoization makes Core about as fast as TcTerm's phase 2,
despite the facts it collects, but so far not faster. For `TermSpec.Lemmas`,
the extra time is in four large `let rec` lemmas over term syntax
(`open_with_gt_ln_spec`, etc.). Their SMT time is 3.7s in `strict` mode
against 1.5s in mode 0.
