# The simplified effect system

*A reference for F\* compiler developers.*

This document describes the representation of computation types in F\* after
`Tot`/`GTot`/`Div` were made primitive and specifications were moved out of
computation types. It covers the core syntax, the invariants every phase relies
on, what each phase does differently, the user-visible consequences, and the
known limitations. It is written for someone changing the compiler, not for
someone writing F\* programs — though the *Migration and idioms* section is
useful for both.

Contents:

1. [What changed](#1-what-changed)
2. [The core representation](#2-the-core-representation)
3. [Primitive effects and effect classification](#3-primitive-effects-and-effect-classification)
4. [Desugaring: where the specification goes](#4-desugaring-where-the-specification-goes)
5. [Effect abbreviations are bare aliases](#5-effect-abbreviations-are-bare-aliases)
6. [The typechecker](#6-the-typechecker)
7. [Universes](#7-universes)
8. [The SMT encoding](#8-the-smt-encoding)
9. [The reflection API](#9-the-reflection-api)
10. [Extraction](#10-extraction)
11. [Resugaring, printing and error messages](#11-resugaring-printing-and-error-messages)
12. [Migration and idioms](#12-migration-and-idioms)
13. [Known limitations and open bugs](#13-known-limitations-and-open-bugs)
14. [Notes for compiler developers](#14-notes-for-compiler-developers)
15. [Regression test index](#15-regression-test-index)

---

## 1. What changed

Before this change, `PURE`, `GHOST` and `DIV` were the primitive effects, each
indexed by a weakest-precondition transformer; `Tot` and `GTot` were
abbreviations of them; *and* `comp'` had dedicated `Total`/`GTotal`
constructors. One concept had three representations, and roughly 140 hardwired
`lident` comparisons existed to keep them in step.

Now:

* **`Tot`, `GTot` and `Div` are primitive**, declared in `Prims`. `Pure`,
  `Ghost`, `Dv`, `PURE`, `GHOST`, `DIV` are ordinary front-end abbreviations
  that the desugarer resolves away.
* **A computation type carries no logical content.** It is an effect name, a
  result type and some flags. There are no WP transformers, no effect indices,
  no `comp_pre`/`comp_post`.
* **A precondition becomes an implicit `squash` binder** on the enclosing
  arrow; **a postcondition becomes a refinement** of the result type.
* **`comp'` has exactly one constructor.** `Total`/`GTotal` are gone.
* **`lcomp` is gone.**
* **Effect abbreviations are bare aliases** and are resolved away in
  `ToSyntax`, so `comp_typ.effect_name` is always a *root* effect.

The point of the exercise is that arrow types can no longer be compared without
comparing their specifications, because the specification is part of the type in
the ordinary way: a binder and a refinement. A whole class of bugs — "this code
path forgot to look at the comp's pre/post" — becomes unstateable.

---

## 2. The core representation

### `comp_typ`

`src/syntax/FStarC.Syntax.Syntax.fsti`:

```fstar
and comp_typ = {
  effect_name        : lident;      (* always a *root* effect *)
  result_typ         : typ;
  flags              : list cflag;
  source_effect_name : lident;      (* what the user wrote; presentation only *)
}
and comp' =
  | Comp of comp_typ
```

Invariants, in order of how much code depends on them:

1. **`effect_name` is always a root effect name.** The desugarer resolves
   abbreviations, so no phase after `ToSyntax` ever needs to unfold an effect
   name. `Env.norm_eff_name`, `Env.lookup_effect_abbrev` and
   `Env.unfold_effect_abbrev` are gone along with their ~50 call sites.
2. **A `comp` carries no logical content.** The `effect_args` list is gone;
   `comp_univs` is gone.
3. **`source_effect_name` is presentation metadata.** Every syntactic equality
   (`eq_comp`, `Syntax.Hash`, the reflection `comp_eq`, `__compare_comp`,
   `denote_comp`) ignores it. It equals `effect_name` whenever no abbreviation
   was used. There is exactly one semantic consumer — see
   [§8.2](#82-recognising-a-lemma) — and that consumer treats it as a fallback.

### Why `comp_univs` went away

`comp_univs` carried the universe instance of a polymonadic effect's `wp`.
About fifty read sites either round-tripped it or fed it to `wp` combinators
that no longer exist. A computation is now an effect applied to its result type
alone, so its universe is recovered from `result_typ`, exactly as for any other
universe-polymorphic type former.

### `cflag`

From five constructors to two:

```fstar
and cflag =
  | SMTPAT    of term            (* a Lemma's SMT patterns, as a list literal *)
  | DECREASES of decreases_order
```

| Removed flag | Replacement |
|---|---|
| `TOTAL` | `PC.is_pure_effect_lid (comp_effect_name c)`, i.e. `U.is_total_comp` |
| `MLEFFECT` | `effect_name = FStar.All.ML`, i.e. `U.is_ml_comp` |
| `LEMMA` | `U.is_lemma_comp` (see [§8.2](#82-recognising-a-lemma)) |

`TOTAL`'s one non-redundant job had been to record that a comp's effect was an
abbreviation rooted at `Tot` (`Lemma`, for instance). Once the desugarer
resolves abbreviations away, `effect_name` answers that directly.

Fallout: `TypeChecker.Util.weaken_flags` became dead, and `mk_bind` lost its
`flags` parameter together with the standing TODO about `bind`'s flags being
inconsistent with the comp it returns.

### `lcomp` is gone

`TypeChecker.Common.lcomp` was

```fstar
{ eff_name; res_typ; cflags; comp_thunk : ref (either (unit -> ML (comp & guard_t)) comp) }
```

The thunk existed to defer expensive WP composition. With no WPs, it is pure
overhead, and it is replaced by the pair it had become:

| Was | Is |
|---|---|
| `lcomp` | `comp` |
| a function returning `lcomp` with a deferred guard | returns `comp & guard_t` |
| `TcComm.lcomp_comp lc` | `lc, Env.trivial_guard` |
| `lcomp_with_binder` | `comp_with_binder = option bv & comp & guard_t` |

Twelve API functions collapse onto their `Syntax.Util` counterparts. Three
retire as identities: `TypeChecker.Util.weaken_precondition`,
`should_not_inline_lc`, `lcomp_has_trivial_postcondition`, plus `Normalize`'s
four `ghost_to_pure_*_lcomp` variants.

**The one care point.** A thunk was forced *inside* the scope of the binders its
guard mentions. `TcUtil.bind` closes a continuation's guard over the bound
variable and weakens it with `x == e`. Rewriting eagerly means handing those
obligations to `bind` explicitly:

* `tc_match` passes `bind_cases`' guard as `bind`'s continuation guard;
* `tc_eqn` weakens and closes each branch's obligations over the pattern
  variables itself.

Get this wrong and an obligation escapes its scope — usually reported as a
`Bound term variable not found` or, under `--defensive error`, Error 290.

**Side effect:** VCs got cleaner, because vacuous quantifiers introduced by the
thunking discipline (`forall (base: nat). base == base ==> P`) are gone. Two
`expect_failure` annotations changed because error recovery got more honest:
`weaken_result_typ` used to record the expected type only on `lcomp.res_typ`,
leaving the thunked `comp` with the rejected type, which produced a spurious
second error. `Bug655.fst` no longer reports a bogus "`GTot` and `STATE` cannot
be composed"; `Bug3213.fst` reports both offending arguments instead of one plus
a cascade.

---

## 3. Primitive effects and effect classification

`ulib/Prims.fst`, at the very top:

```fstar
total assume effect Tot
total assume effect GTot
assume sub_effect Tot ~> GTot
```

`Div` is declared in `FStar.Pervasives`, as is `NDET`. The lattice is
`Tot ~> GTot`, `Tot ~> NDET ~> Div`, with `NDET ~> TAC`.
`Env.update_effect_lattice` closes the lattice transitively as each edge is
added, so the direct `Tot ~> Div` edge is not written.

### The two kinds of question

There are two different questions about an effect name, and `FStarC.Parser.Const`
keeps them apart deliberately:

* **Class predicates** — `is_pure_effect_lid`, `is_ghost_effect_lid`,
  `is_div_effect_lid`, `is_ndet_effect_lid`. These accept *every spelling*:
  `is_pure_effect_lid` is true of `Tot`, `PURE` and `Pure`. Use them when you
  mean "does this computation diverge?", "is this erasable?", and so on.
* **Identity predicates** — `is_tot_lid`, `is_gtot_lid`, `is_tot_or_gtot_lid`.
  These are the narrow question a match on the old `Total`/`GTotal`
  constructors used to ask: *is this literally `Tot`?* Use them where the
  representation matters — printing, resugaring, the reflection view, deciding
  whether an arrow codomain can be flattened into a spine.

`PC.primitive_pure_lid`, `primitive_ghost_lid`, `primitive_div_lid` and
`primitive_ndet_lid` name the spelling `Prims`/`Pervasives` actually declares.
**Code that *constructs* a comp must use these**, never a spelling directly, so
that changing which spelling is primitive is a one-line change.

`Syntax.Util` wraps all of this so that a caller holding a `comp` never reaches
for the effect name: `is_named_tot`, `is_named_gtot`, `is_named_tot_or_gtot`,
`is_total_comp`, `is_tot_or_gtot_comp`, `is_bare_tot_or_gtot_comp`,
`is_bare_total_comp`, `is_pure_comp`, `is_pure_or_ghost_comp`, `is_ml_comp`.

`NDET` is both a lift source and a lift target, so it cannot be folded into
either neighbouring class; a site that accepts "pure or ndet" and one that
accepts "ndet or div" are asking different questions and both occur in the tree.

> **Inconsistency, left deliberately.** `NDET` is the primitive spelling with
> `Ndet`/`Nd` as abbreviations, which is the opposite of the convention here
> (`Tot`/`GTot`/`Div` primitive, `PURE`/`GHOST`/`DIV` abbreviations). Renaming
> it is churn that belongs in its own change.

---

## 4. Desugaring: where the specification goes

`ToSyntax.desugar_comp` returns a `comp` **and** the precondition it could not
put in the comp. The caller decides what to do with it, and there are exactly
two callers:

| Position | `E t (requires P) (ensures Q)` becomes |
|---|---|
| Arrow codomain | `... -> #(_ : squash P) -> E (x:t{Q x})` |
| Ascription | assert `P` here, and ascribe `E (x:t{Q x})` |

Both are suppressed when trivial: a `requires True` produces no binder at all,
and `U.refine_with_post` returns `t` unchanged for a trivial post.

**The precondition binder goes *last*.** It has to: `P` may mention the explicit
binders. This is the single most consequential representational choice in the
whole change, because it means an arrow with a `requires` has one binder *more*
than an otherwise identical arrow without one, and that binder is implicit. See
[§6.3](#63-eta-expansion-across-an-arity-mismatch) and
[§12](#12-migration-and-idioms).

### `refine_with_post` and its inverse

```fstar
val refine_with_post      (t:typ) (p:term) : ML typ   (* x:t{p x}, or squash (p ()) *)
val post_of_result_typ    (t:typ)          : ML term  (* partial inverse *)
```

`refine_with_post t p` returns `x:t{p x}`, except that when `t` is `unit` and
`p` does not mention its argument it returns `squash (p ())`. That special case
is why a `Lemma`'s result type is `squash Q` rather than `_:unit{Q}`, and it has
consequences all over the encoder and the reflection API.

`refine_with_post` runs on **unelaborated** syntax, where `Tm_unknown` holes are
everywhere. Anything in it that uses `term_eq` must first check `term_eq t t`,
because `term_eq` deliberately gives up on a hole — two holes need not elaborate
to the same term. Failing to do this leaves stray beta-redexes in types, which
defeats the syntactic matching that typeclass resolution performs. (This was a
real bug: it bootstrapped stage 1 fine and failed stage 2 with
`Could not solve typeclass constraint 'monad (fun _ -> _: m (*?u*)_ {(fun _ -> l_True) _})'`.)

### `sort_comp_args`

`ToSyntax` has a single classifier for "which argument of an effect application
is the result type, which is the pre, which is the post":

```fstar
let sort_comp_args (is_lemma:bool) (args:list (AST.term & AST.imp)) : ML (option comp_args)
```

It partitions out universe applications, `requires`, `ensures`, `decreases` and
(only when `is_lemma`) `SMTPat` arguments, allows at most one of each, and then
assigns whatever is left positionally. `None` means "not a shape we recognise";
the caller reports it, since the caller knows which effect is being applied.

Both `desugar_comp` and `comp_requires` are driven from it. Previously
`comp_requires` scanned for an index that had to agree with `desugar_comp`'s
classification but shared no code with it, and `desugar_comp` classified twice.
That drift was a real source of bugs: a definition could acquire a binder its
`val` lacked.

Note the consequence for `Lemma`: in this scheme `Lemma` is simply *the effect
with no result type that may carry SMT patterns*. Nothing else accepts an
`SMTPat` argument, which is what makes the `SMTPAT` flag a reliable structural
mark ([§8.2](#82-recognising-a-lemma)).

A **universe application on an effect** (`Tot u#0 int`) is now rejected rather
than accepted and silently discarded. There is nowhere left to record it, and
nothing it could say that the result type does not already.

### `Lemma`

`Lemma` is declared as

```fstar
effect Lemma (a: Type) = Tot a
```

and

```fstar
val f (bs) : Lemma (requires P) (ensures Q) [SMTPat pats]
```

desugars to

```fstar
bs -> #(_ : squash P) -> Tot (squash Q)
```

with `flags = [SMTPAT pats]` and `source_effect_name = Prims.Lemma`.

Two things follow:

* **The post-thunking hack is gone.** `thunk_ens`, `unthunk` and
  `unthunk_lemma_post` are deleted. Issue #57's reason for thunking — assume `P`
  while checking the well-formedness of the post — is served by the `squash P`
  binder standing to the *left* of the result type.
* **`Tot (squash phi)` and `Lemma (ensures phi)` are now the same type**, so the
  bespoke subtyping rule that related that pair is deleted. This is why
  `Classical.forall_intro` and friends now accept a `Lemma`-typed field
  directly, and why many vacuous `Classical.move_requires` wrappers in ulib
  could be deleted.

---

## 5. Effect abbreviations are bare aliases

An effect abbreviation is a renaming of one effect name by another, and nothing
else. The canonical form is

```fstar
effect M = N
```

The eta-expanded `effect M (a:Type) = N a` is still accepted, because stage0 has
to parse ulib. **Everything else is rejected with Error 316**
(`Fatal_EffectAbbreviationResultTypeMismatch`): extra binders, a right-hand side
that is not an eta-expansion of an effect name (`effect A a = Tot (list a)`), or
a `requires`/`ensures` on the right-hand side.

Previously an abbreviation could take binders and give its right-hand side a
specification (`effect MyTot (a:Type) = Tot a (ensures fun _ -> False)`).
Neither could mean anything — a `requires` on an abbreviation would have to
become an implicit binder on the *arrow* whose codomain the abbreviation is used
at, and an abbreviation has no arrow of its own. Commit `7e71460e09` had *added*
`ensures` support; this reverses it. Pinned by
`tests/bug-reports/closed/Bug1370b.fst`.

### What this removed

* `Env.norm_eff_name` (~50 call sites), `Env.lookup_effect_abbrev`,
  `Env.unfold_effect_abbrev`, `TcEffect.tc_effect_abbrev`.
* `eff_decl.univs` and `eff_decl.binders`.
* The `TOTAL` and `LEMMA` flags.
* `Sig_effect_abbrev` shrinks to `{ lid : lident; root : lident }`. It is kept
  only so that a module read back from a `.checked` file can rebuild its
  `DsEnv`; the core syntax does not otherwise mention it.

### Neighbouring surface-syntax removals

* **`redefine_effect`** (`effect M = N <: ...`) is gone from the grammar. It was
  the only other production for `NEW_EFFECT`.
* **The `[attributes ...]` clause** on an effect abbreviation or redefinition is
  gone: the `ATTRIBUTES` token, the production, the `Attributes` surface-AST
  node, and the `cattributes` plumbing in `ToSyntax`. The only flag it could
  produce was `CPS`, which went away with Dijkstra Monads for Free
  (`7e468aa485`).
* **A `sub_effect` must name effects, not abbreviations.** `sub_effect PURE ~> M`
  used to work only because `ToSyntax` resolved the name; write
  `sub_effect Tot ~> M`. The error message names the effect the abbreviation
  stands for.

### Two traps this uncovered

Two places built syntax by hand that named an *abbreviation* where a root effect
is required. They worked only because `norm_eff_name` cleaned up afterwards:

* `Pulse.Extract.CompilerLib`, naming `DIV` and `PURE`;
* `Syntax.Util.is_ml_comp` and the `fail_exp` let-binding, naming `ML`.

If you are writing code that constructs a `comp`, use `PC.primitive_*_lid`.

---

## 6. The typechecker

### 6.1 Getting a variable out of a type

When `bind` eliminates a binder, facts about that binder that were recorded in
the result type have to go somewhere. Five converging changes:

* **Recover, don't drop.** Escaping variables are quantified *existentially*
  rather than deleted; simplification then applies the one-point rule. `_ == x`
  with `x : nat` becomes `_ >= 0`; `_ == f x /\ x == 3` recovers as `_ == f 3`.
  The whole formula is closed at once, not conjunct by conjunct: with `y`
  escaping, `x == y /\ y == z` recovers as `x == z`, which per-conjunct closing
  would destroy. Quantified binders' sorts are normalized, because the one-point
  rule restates the eliminated binder's typing hypothesis and cannot see through
  an abbreviation — that is what turns `nat` into `_ >= 0`.
* **Decline to introduce, for `let rec`.** `exists (f: a -> b). _ == f n` is
  witnessed by any constant function, while putting a higher-order quantifier in
  every derived type. `Env.rec_names` records the names bound by the enclosing
  `let rec`, and four points in `TypeChecker.Util` consult it: `should_return`,
  `bind_result_subst`, the pure-substitution branch of
  `eliminate_binder_from_typ`, and `captured_typing`.
* **One authority.** `check_no_escape` and `escape_cause` moved from `TcTerm`
  into `TypeChecker.Util`. `eliminate_binder_from_typ` sees through `squash` and
  other abbreviations, closes what it can existentially, and discards conjunct
  by conjunct rather than wholesale.
* **Never substitute an impure term into a type.** The last-resort branch used
  to substitute the bound term, which is exact for a pure or ghost term and
  wrong for an effectful one, which may diverge and need not produce the same
  value twice. Instrumenting it finds it reachable: one hit across ulib and the
  test suite, at `tests/extraction/Micro.fst` with `c1 = Div`, where it produced
  `squash (f11 (g11 x) == g11 x)` — a type mentioning a `Div` application, which
  no source program could write.
* **Split the driver.** `bind_maybe_capture` had grown to ~500 lines conflating
  four jobs. The driver is now 34 lines; `composite_result_typ` is the sole
  authority on the result type, and its two ways of getting rid of the binder
  are separated: `bind_result_subst` substitutes `e1`,
  `eliminate_binder_from_typ` closes `x` existentially when it cannot.

The type side and the guard side do **not** conflict, and the asymmetry is
deliberate: *types are closed by substitution, formulas by quantification*. The
substitution rewrites the result type, where `x` is not bound; the `x == e1`
equation goes on the guard under `Env.close_guard`, where `x` deliberately
stays.

### 6.2 `Meta_monadic` records the bare type

`Meta_monadic` and `Meta_monadic_lift` annotate a monadic `let`/application with
its result type, as a hint for reification and extraction. `tc_term` drops the
annotation on re-check and extraction ignores it.

Recording the *inferred* type now means recording a postcondition that embeds
the very terms it describes. The copies nest, so elaborated terms grew
*multiplicatively* with nesting depth, and anything that walks a term became
exponential: `tests/bug-reports/closed/Bug3210.fst` went **0.52s → 1214s**, and
`FStar.Tactics.Visit.fst.checked` went from 151KB to 546KB.

Fix: record the bare type (`5f60b4c352`). Bug3210 is back to 0.57s and the
checked file to 255KB.

### 6.3 Eta-expansion across an arity mismatch

A precondition is a trailing implicit binder, so `Pure t (requires p)` has one
binder more than `Tot t`. `tc_abs` inserts a missing implicit for a *lambda*,
but a point-free term had no way to bridge the gap.

`TypeChecker.Util.try_eta_expand_to_expected_typ` now handles **both**
directions: the term's type having fewer binders than expected, and having
*more*, all of them implicit (which is where an *application* lands). `e` is
applied to the shorter of the two arities' worth of arguments, taken from the
term's own type — whose sorts are concrete, where the expected type's may still
be uvars — while the abstraction binds *all* of the expected type's binders,
since `tc_abs` only ever inserts *leading* implicits and the ones at issue are
trailing.

It has to run **before** the subtyping check, not only in its failure branch:
relating `x:a -> Tot b` to `x:a -> #_:squash p -> Tot b` does not fail, it
succeeds with an unprovable `has_type b (#_:squash p -> Tot b)` obligation. So
`weaken_result_typ` tries it up front on types that are already syntactically
arrows (so the common case costs nothing), and again after subtyping has failed,
that time normalizing first.

Eta-expanding an effectful term would delay, duplicate or drop its effect, so
both hooks are guarded by `is_pure_or_ghost_comp`.

There is a second, narrower use: `Classical.move_requires` applied to a lemma
with **no** `requires`. Such a lemma has one binder fewer than `move_requires`
expects, and `move_requires`' argument binder is `$_:`, i.e. `Equality`, which
forces `use_eq` and rules out ordinary subtyping.
`try_eta_expand_to_expected_typ` rebinds a trailing expected binder whose sort
is `squash ?p` with `?p` *uvar-headed* at `squash True`, letting `?p := True`
fall out of the ordinary check. A **concrete** expected precondition is left
alone, so genuinely strengthening a precondition is still rejected.

### 6.4 `dedup_vc`

A `requires` is a binder, so the obligation attached to an implicit `squash`
argument is closed over the binders in scope and conjoined into the same VC as
the body's obligation, rather than being solved and discharged in a nested
`push`/`pop` frame. Identical copies accumulate, once per elaboration path.

The symptom is contextual, not semantic: for `FStar.Math.Lemmas.lemma_div_plus`,
the SMT text of the query was *byte-identical* before and after an unrelated
upstream merge, and bare `z3` solved it in 0.9s, but the goal went from **0.087
rlimit to exhausting 5.000** — a ~57x blow-up. Its VC carried **32
syntactically identical copies** of the guard `n > 0 ==> n <> 0`, nested under
seven layers of `forall (_: Prims.unit)`.

`Rel.dedup_vc` walks the conjunctive structure of a VC and replaces a conjunct
by `True` when a syntactically identical conjunct has already been seen in a
*goal* position that dominates it. Correctness argument:

* It is sound because the retained occurrence is proved outright, so the dropped
  one follows from it.
* The set of known conjuncts only ever travels **downwards** — into the right of
  a conjunction, the conclusion of an implication, and the body of a quantifier
  — so a conjunct found under a binder is never assumed known outside it.
* Pushing the outer set *under* a binder is fine: those conjuncts are well
  scoped in the enclosing context and therefore mention none of the bound
  variables, and `SS.open_term_1` picks globally fresh names, so capture is
  impossible.
* Membership uses `FStarC.Syntax.Hash`'s structural `equal_term`, not a hash
  comparison, so a collision costs a missed opportunity and never an unsound
  drop.

It runs at the single point in `do_discharge_vc` where a goal is handed to
`env.solver.solve` — after tactic preprocessing, after normalisation, and after
`check_trivial` — so nothing upstream of the solver can observe it and it cannot
perturb unification, inference or tactics. `FSTAR_NO_DEDUP_VC=1` turns it off,
which makes attributing a regression to it mechanical.

Measured on `FStar.Math.Lemmas`: 1071 goals → 654; `lemma_div_plus` 41 goals →
10; 7.8s → 8.4s wall.

The one visible cost: two failing obligations at two source lines can now
collapse to one message. `tests/bug-reports/closed/Bug3213b.fst` moved from
`expect_failure [19;19;19]` to `[19;19]` for exactly this reason. Labelled goals
are unaffected, since `equal_term` compares the range inside `Meta_labeled`, so
only unlabelled duplicates merge.

**This is a narrower fix than the problem deserves.** It removes the duplicates
at the end rather than avoiding their construction, so `Env.push_guard` still
does the redundant work. Scoping the guards at construction is still worth
doing.

### 6.5 Other typechecker fixes carried by this work

Several of these are latent upstream and were surfaced, not caused, by the
refactor.

* **A failed precondition is reported at the call, not at the definition**
  (`dc401f3935`). `check_implicit_solution_and_discharge_guard` discharged the
  guard with whatever range the environment happened to carry when the implicit
  was finally resolved, typically the enclosing definition. The range is now the
  implicit's own introduction site — which matters directly, since every
  precondition is now such an implicit.
* **The normalizer can compute universes of types that mention local binders**
  (`a198fab809`). The normalizer tracks the local scope in its own closure
  environment and never extends `cfg.tcenv`, so a type read off a residual comp
  or a monadic lift annotation may mention variables `tcenv` has never heard of.
  Harmless while comps carried no logical content; now a result type routinely
  mentions the binders its postcondition talks about, and
  `reify_bind`/`reify_lift`'s calls to `universe_of` trip the defensive
  well-scopedness check (Error 290). Free variables are reintroduced from the
  sorts they already carry before asking for the universe; a universe is
  determined by sorts alone, so no result changes.
* **`has_type` was instantiated at `u#0` twice** (`691d7c8598`). Only
  `Rel.guard_of_prob` was still on that path, and the SMT encoder *does* encode
  universe arguments, so a formula about `x <: t` at any other universe was
  encoded against a symbol nothing else mentions. Both universes are now
  computed at that site; `mk_has_type_us` takes them, and `mk_has_type` is the
  `u#0`-only convenience for callers that only build a formula for the encoder.
* **A refinement was dropped when joining two lower bounds under unsolved
  universes.** Two structurally identical refinements can differ only in the
  universe uvar of an `eq2`; `U.term_eq` compares universe uvars by identity, so
  `combine_refinements` concluded the bounds were genuinely different and
  widened to the base type. It now falls back to `try_eq` **on the two
  refinement formulas** when `term_eq` says no. `try_eq` runs with
  `smt_ok=false`, so it can only unify structurally-equal formulas modulo
  universe solving; applying it to the whole types instead would wrongly
  identify `t` with `t{phi}`.
* **A flex variable with a refined *and* an unrefined upper bound** was solved
  to their meet, making the refinement part of the variable's definition and
  then asking every *lower* bound to prove it at its own source position.
  `let y = match ... in lem y; y` is enough to hit it. Deferring is right — with
  the wrinkle that deferring a problem removes it from `wl.attempting`, hiding
  the very bound that motivated the deferral, so deferred problems must be
  counted as bounds too.
* **Uvars in implicit positions are not logical content.** `Rel` rewrites
  `squash p <: squash q` into `(_:unit{p}) <: (_:unit{q})`, which is what makes
  such a check cheap, and the rewrite was guarded by "neither side contains a
  uvar". An incidental *implicit* uvar — the `#a:eqtype` of `op_Equals` — was
  enough to disable it, sending the problem to `Tm_app` congruence, whose local
  `equal` helper normalises with `[UnfoldUntil delta_constant; ...]`; unfolding
  `to_vec`/`from_vec` at width 64 then consumed 32 GB and did not terminate.
  The guard is now `has_uvar_needing_congruence`: a uvar that is an implicit
  argument of an *interpreted* head can be ignored; every other uvar is logical
  content and must still block the rewrite. **The restriction to interpreted
  heads is load-bearing**: an intermediate "ignore a uvar in any implicit
  position" version broke EverParse, by turning a `squash <: squash` problem
  that used to solve an implicit by congruence into an SMT implication that
  solves nothing, so the implicit survived typechecking and was *generalized*.
  An earlier "no flex at all" formulation broke `introduce _ ==> _`, because
  `FStar.Classical.Sugar.implies_intro`'s `p` and `q` *are* explicit.
* **`TypeChecker.Core` accepts an unelaborated `let` inside a type.** Core's
  `Tm_let` case typechecked `lb.lbtyp` unconditionally, but a `let` occurring
  inside a *type* can still carry the `Tm_unknown` the desugarer left there.
  Core now falls back to the definition's inferred type when the annotation is
  absent, which is sound: an unannotated `let`'s type *is* its definition's
  type, and the subtyping check it would otherwise perform is reflexive. The
  hole is intentional and confined to `lb.lbtyp`: `TcTerm.check_inner_let` keeps
  `lbtyp = tun` when the source had no annotation, because phase 1 discards
  specifications and phase 2 reads `lbtyp` back as if it were a source
  annotation — recording phase 1's coarser type would throw away the
  postcondition. Reached in practice only through Pulse.
* **A `let rec` whose result is a function kept its `ensures`.** An `ensures` is
  a refinement on the result type, so a definition returning a function is
  annotated with a *refinement of an arrow*. `Syntax.Util.arrow_formals_comp`
  deliberately looks *through* such a refinement and throws the predicate away —
  harmless for a caller that only counts binders, fatal for one that rebuilds a
  type. Two did: `TcUtil.extract_let_rec_annotation` (which was checking the
  body against the unrefined arrow) and `TcTerm.guard_letrecs` (which was hiding
  the definition's own postcondition from its recursive calls).
  `Normalize.get_n_binders_no_unrefine` splits with the strict splitter, falling
  back to the old one only when that finds too few binders, so it can never see
  less than before.
* **`Rel.imitate_arrow` / `compress_cprob`**: with `Total` gone, the whnf of a
  comp is `Comp ct` guarded by `U.is_bare_tot_or_gtot_comp`; there is no
  constructor to match on.
* **A top-level definition records its declared type, not its body's type.**
  `let my_int : Type = int` was being recorded at `eqtype`. Keeping the sharper
  type is right *inside* a definition and wrong at its boundary, where it
  publishes an implementation detail as the signature — and defeats
  `FStar.Tactics.Parametricity`.
* **`tc_pat` no longer emits `FStar.Pervasives.id (proj x)`** for a pattern
  variable. Only beta-reduction runs before that term reaches the branch's
  result type, so the `id` survived and blocked the projector equation. An
  identity lambda beta-reduces away.
* **A postcondition reaches its continuation** even when the bound variable does
  not occur in the continuation's result type, as in `hd :: f tl`.
* **`--ext optimize_let_vc` is inert** (`f8a8e05784`). Keeping a let-bound
  variable opaque in the VC — `forall x. x == e ==> phi` rather than `phi[e/x]`
  — is no longer optional, and there are no layered effects left in `bind` to
  accommodate. The key defaulted to true and nothing in the tree set it to
  false, so the disjunct it guarded was constantly false. Flags still passed by
  Pulse, `examples` and karamel become inert rather than wrong.
* **`mk_imp_simp`/`mk_conj_simp` in `Rel.solve_t'`.** The refinement/refinement
  case builds `forall x. phi1 ==> True` when the right-hand side is unrefined
  (`force_refinement` turns `Tot u32` into `x:u32{True}` purely to match
  shapes). `mk_conj`/`mk_imp` do not simplify, so `simplify_vc` normalized a
  trivial antecedent — exponentially, for a chain of `let`s over a `match`.
  `Bug3800.fst` went 0.47s → 6.18s on this path and is now 0.31s, i.e. faster
  than before. `EQ` is deliberately left alone: `phi1 <==> True` is `phi1`, not
  `True`.
* **A failed plugin reduction no longer corrupts the term** (`fc8dbb0d71`).
  When a native plugin cannot unembed its arguments because they are still
  symbolic, `arrow_as_prim_step_N` fell back to a "shadow" application rebuilt
  from the arguments its generated wrapper handed it, which exclude the
  universes and leading type arguments the wrapper stripped off. `sel #int r 1`
  came back as `sel r 1`; `reduce_primops` accepted that as a reduction, after
  which the term could never reach the primitive step again. Latent upstream;
  the primitive-effect flip made it reachable (and OOM-killed
  `examples/native_tactics/Registers.List.Test` in CI).
* **A native tactic's `.cmxs` is rebuilt when the compiler changes**
  (`f31316706f`). `load_native_tactics` compiles a plugin's extracted `.ml` only
  when the `.cmxs` is *absent*. The stamps depend on `$(FSTAR_EXE)`, so the
  objects are dropped there now; previously every test in such a directory
  failed with Error 353 after a compiler rebuild.
* **`fstar.exe -c M.fst -o M.fst.checked` no longer consults the cache** to
  decide whether to load dependences on the fly. `-o` makes `tc_one_file`
  recheck `M` from source regardless, so a stale-but-valid `M.fst.checked`
  silently switched `M` to the non-incremental path, which typechecks the module
  only after its whole desugaring is finished — and finishing pops the module's
  `open`s off the scope that tactics read out of the environment.
  `tests/tactics/BQual.fst` printed `Prims.int` for `int`; `Parsing.fst` could
  not resolve `+`. Both passed from a clean tree and failed on the second build.

---

## 7. Universes

`TcUtil.universe_of_comp` used to say: *if `M` is pure or ghost, or is marked
total, then `u_res`, else `u#0`.* That is **unsound** for a total effect whose
`repr` does not preserve universes. With

```fstar
repr (a:Type u#a) : Type u#(max a 1) = (t:Type u#0 & a)
```

`M bool : Type u#1`, but the old rule said `u#0`, letting `unit -> M bool` pass
as a `Type u#0` — an embedding of `Type u#0` into `Type u#0`.

`FStarC.TypeChecker.Core.check_comp` already had it right. Both now share
`Env.effect_universe`.

`TcEffect.tc_eff_decl` reads the universe off `repr` once at declaration time
and stores it as `eff_combinators.repr_universe`, the scheme
`[u_a]. Type u#r where repr u#u_a a : Type u#r`.

This cuts both ways: with `repr (a:Type u#a) : Type u#0 = bool`,
`unit -> M (Type u#5)` is correctly a `Type u#0`.

Unchanged: a **partial** effect still answers `u#0` (`unit -> Dv t : Type0`);
`Tot`, `GTot` and any `total assume effect` have no repr and answer with the
result type's universe. `NDET` is `total` with no representation, so
`unit -> Nd (Type u#0)` is still `Type u#1`.

This was a **pre-existing bug** — the same three lines are upstream. Pinned by
`tests/micro-benchmarks/SimpleEffects_ReprUniverse.fst`.

---

## 8. The SMT encoding

### 8.1 A `Lemma`'s axiom is byte-for-byte unchanged

This was the main risk of the whole change: ulib and downstream code contain
~5300 `Lemma` occurrences, ~1080 of them with a `requires`.

The encoder recovers everything it needs structurally:

* `pre` from the trailing `squash`-typed implicit binder,
* `post` from the argument of `squash`,
* the quantifier ranges over the **real** binders only.

For

```fstar
val lem (x:int) : Lemma (requires p x) (ensures q (f x)) [SMTPat (f x)]
```

the emitted axiom is

```smt2
(assert (! (forall ((@x0 Term))
  (! (implies (and (HasType @x0 Prims.int) (Valid (L.p @x0))) (Valid (L.q (L.f @x0))))
   :pattern ((L.f @x0)) :qid lemma_L.lem)) :named lemma_L.lem))
```

which is the shape the previous design produced. Verified across no-`requires`
lemmas, multi-binder lemmas with `SMTPatOr`, universe-polymorphic lemmas with
fuel instrumentation, and lemmas with a quantified `ensures`.

`Syntax.Util.split_squash_binders` is the helper that does the split:

```fstar
val split_squash_binders (used:list term) (bs:binders) : ML (binders & term)
```

**`used` is not optional.** An earlier version treated *any* trailing implicit
`squash` binder as the anonymous precondition binder, so a user-written
`(#h:squash True)` mentioned in an `ensures` or in an SMT pattern was removed
from the binder list while its name was still live, crashing the checker with
`Bound term variable not found h`. The binder is dropped only when its name is
free in none of `used`. `destruct_lemma_with_smt_patterns` passes the result
type and the patterns; `TcTerm.check_smt_pat` does the same.

### 8.2 Recognising a lemma

A definition whose type is a lemma is encoded as an **axiom** rather than as an
equation. Two places decide this, and they must agree:

* `SMTEncoding.Encode.encode_top_level_let` routes a `let` to
  `encode_top_level_vals` when `U.is_lemma lb.lbtyp` holds;
* `U.is_smt_lemma` decides whether the SMT patterns get validated and used.

Both are now **structural**, sharing one helper:

```fstar
val comp_has_smt_pats (c:comp) : ML bool

let is_lemma_comp c =
     lid_equals ct.source_effect_name PC.effect_Lemma_lid
  || (PC.is_tot_lid ct.effect_name && comp_has_smt_pats c)

let is_smt_lemma t = PC.is_tot_lid ct.effect_name && comp_has_smt_pats c
```

The reasoning: `sort_comp_args` partitions `SMTPat` arguments only when
`is_lemma`, so a non-empty `SMTPAT` flag is *exactly* the image of a source
`Lemma ... [SMTPat ...]`. This also puts these two in agreement with
`destruct_lemma_with_smt_patterns` and `smt_lemma_as_forall`, which build the
axiom and already keyed off the flag alone.

`source_effect_name` is still consulted, as a fallback, for a **pattern-less**
`Lemma`: once desugared it is literally `Tot (squash p)` and carries no other
mark. That fallback is why the field is not purely presentational.

Why this matters: a `Lemma` built *by reflection* (a splice, a tactic) will
generally leave `source_effect_name` at `Tot`, and used to silently stop being a
lemma. `tests/bug-reports/closed/Bug2596b.fst` pins the structural path: it
splices a lemma whose `source_effect_name` is `Tot`, and the `SMTPat` still
fires.

`is_smt_lemma` deliberately does **not** also require a squashed postcondition.
`Lemma True [SMTPat …]` desugars to result type `unit`, not `squash`, because
`refine_with_post`'s trivial-post shortcut returns `t` unchanged; requiring
`squash` would stop `check_smt_pat` from validating those patterns, for no gain.

### 8.3 `.checked` files cache the SMT encoding

A `.checked` file caches not only a module's typechecked declarations but **its
SMT encoding** (`encode_modul_from_cache`). Since `.checked` files are not tied
to the compiler that produced them, a change to `FStarC.SMTEncoding.*` has no
effect at all on any module whose artifact is already on disk — including all of
ulib. Measuring such a change means deleting `stage{1,2,3}/ulib.checked` (and
`fstarc.checked`, or the rebuild fails with Error 317), not just rebuilding the
compiler.

---

## 9. The reflection API

### The view

`ulib/FStar.Stubs.Reflection.V2.Data.fsti` mirrors `comp_typ` field for field:

```fstar
noeq type decreases_order =
  | Decreases_lex : list term -> decreases_order
  | Decreases_wf  : term -> term -> decreases_order

noeq type cflag =
  | SMTPAT    : term -> cflag
  | DECREASES : decreases_order -> cflag

noeq type comp_view = {
  effect_name        : name;
  result_typ         : typ;
  flags              : list cflag;
  source_effect_name : name;
}
```

The old view was an inductive — `C_Total`, `C_GTotal`, `C_Lemma`, `C_Eff` —
describing a computation type that no longer exists. It exposed a precondition
(now an implicit `squash` binder on the arrow, out of a comp's reach) and a
universe list (an effect is applied to its result type alone), and it forced
`inspect_comp` to canonicalise effect names.

That was a **soundness bug**, not just an infelicity. The round-trip axiom

```fstar
val inspect_pack_comp_inv (cv:comp_view)
  : Lemma (requires (match cv with
                     | C_Eff us eff_name _ _ _ _ -> Nil? us /\ eff_name <> Lemma
                     | _ -> True))
          (ensures inspect_comp (pack_comp cv) == cv)
```

did not restrict enough: `pack_comp` also drops a `C_Eff`'s `pre` and `post`,
and `inspect_comp` rewrites `Prims.Tot` to `C_Total`. Both functions are
primitive normalizer steps, so the normalizer refutes the axiom directly:

```fstar
let bad () : Lemma False =
  let cv = C_Eff [] ["Prims"; "Tot"] (`int) (`l_True) (`(fun _ -> l_True)) [] in
  inspect_pack_comp_inv cv   (* inspect_comp (pack_comp cv) reduces to C_Total (`int) *)
```

With the record, `inspect_comp` is a projection and `pack_comp` an injection —
no canonicalisation, nothing invented, nothing dropped — so both

```fstar
val pack_inspect_comp_inv (c:comp)       : Lemma (pack_comp (inspect_comp c) == c)
val inspect_pack_comp_inv (cv:comp_view) : Lemma (inspect_comp (pack_comp cv) == cv)
```

hold with **no precondition**, and `FStar.Reflection.Typing`'s `SMTPat`-carrying
mirror (which is what Pulse uses) is likewise unrestricted.

### Helpers

In `FStar.Stubs.Reflection.V2.Data`:

```fstar
let tot_effect_name  : name = ["Prims"; "Tot"]
let gtot_effect_name : name = ["Prims"; "GTot"]

let mk_comp_view (eff:name) (res:typ) : comp_view
let mk_tot_comp  (res:typ) : comp_view
let mk_gtot_comp (res:typ) : comp_view

let is_tot_comp         (cv:comp_view) : bool
let is_gtot_comp        (cv:comp_view) : bool
let is_tot_or_gtot_comp (cv:comp_view) : bool
```

Because the desugarer resolves abbreviations away, `effect_name` is a root
effect and can be compared literally.

Note that `is_tot_comp` keys off the effect name **only**, so a `Tot` carrying a
`decreases` is total — the old `inspect_comp` reported `C_Eff` for it.

### Extraction constraint

`mk/fstar-01.mk` and `mk/fstar-12.mk` carry `EXTRACT += --extract -FStar.Stubs`,
and `src/extraction/FStarC.Extraction.ML.UEnv.fst` maps
`"FStar"::"Stubs"::rest when plug ()` to `"FStarC"::rest`. Consequently **every
`let`, constructor and type used by `FStar.Stubs.Reflection.V2.Data` must also
be declared in `src/reflection/FStarC.Reflection.V2.Data.{fsti,fst}`**, with the
same names and the same definitions. The compiler-side mirror is not optional
and is not merely a convenience; plugin extraction resolves through it.

`source_effect_name` is carried through verbatim by both directions and is
ignored by `comp_eq`, `__compare_comp` and `denote_comp`, all of which are about
a comp's meaning.

### Migrating a client

| Old | New |
|---|---|
| `C_Total t` (match) | `is_tot_comp cv` and `cv.result_typ` |
| `C_GTotal t` | `is_gtot_comp cv` |
| `C_Total t` / `C_GTotal t` (construct) | `mk_tot_comp t` / `mk_gtot_comp t` |
| `C_Lemma pre post pats` | `cv.result_typ` is `squash Q`; `pre` is a binder on the arrow; `pats` is in `cv.flags` |
| `C_Eff us eff t pre post fl` | `mk_comp_view eff t`, then set `flags` |

`tests/tactics/CompRoundTrip.fst` checks *by computation* that
`inspect_comp (pack_comp cv) == cv` for `Tot`, `GTot`, an arbitrary effect, a
comp whose `source_effect_name` differs from its `effect_name`, and a comp
carrying `SMTPAT`, `Decreases_lex` and `Decreases_wf` flags, and it instantiates
both axioms at arbitrary arguments.

> A note worth keeping: the *old* version of that test asserted the `C_Eff`
> round trip and passed, because it proved its goal with `trefl`, and `trefl`
> will equate two syntactically different quoted terms. That is pre-existing
> upstream behaviour — it reproduces on `master` and on a released binary — but
> it is why a false test looked green. Prefer checking a round trip *by
> computation* (`assert_norm`, or a boolean equality that must reduce to `true`)
> over `trefl` on quoted terms.

---

## 10. Extraction

A `#(squash P)` binder carries no computational content, so extraction drops it
— both the binder and the matching argument — and **the ABI of a function with a
`requires` clause is unchanged**.

Three pieces have to agree:

* `is_spec_binder` recognises the binder;
* `binders_as_ml_binders` drops it from a lambda;
* `drop_spec_args` drops the matching argument from an application.

### `is_spec_binder` is type-directed, deliberately

It erases *any* implicit `squash` argument, not only the ones the desugarer
inserts. This is not observable: `squash p` is `x:unit{p}`, so an argument of
that type carries no information whatever its provenance, and a *use* of such a
variable extracts to `()` whether or not its binder was kept:

```fstar
let h (#s : squash (1 == 1)) (x:int) : int & squash (1 == 1) = (x, s)
let use () : int & squash (1 == 1) = h #() 3
```
```ocaml
let h (x : Prims.int) : (Prims.int * unit) = (x, ())
let use (uu___ : unit) : (Prims.int * unit) = h (Prims.of_int 3)
```

The higher-order case stays consistent because the *type* is erased by the same
predicate: `#s:squash (1 == 1) -> int -> int` extracts to
`Prims.int -> Prims.int`, so a lambda, an application and a value of that type
all agree.

Attributing the desugarer's binder instead would be a one-line change at its
single construction site in `ToSyntax`, but it would make erasure depend on
*provenance* rather than on type, and provenance is easy to lose: every path
that rebuilds an arrow would have to preserve the attribute — `Syntax.Util`'s
arrow constructors, `Pulse_Extract_CompilerLib`, the reflection API's
`mk_arrow`, and `TcUtil.extract_let_rec_annotation`, which already demonstrably
drops a refinement it does not know about. A single miss is silent: that one
definition keeps the argument while its callers drop it — exactly the ABI
inconsistency a type-directed predicate cannot produce. It would also need
`cache_version_number` bumped, since a `val` checked before the change and a
`let` checked after would disagree.

If the attribute is wanted anyway, the right form is a marker in `Prims` (a
`requires` inside `Prims.fst` itself must be able to mention it) plus a check in
`is_spec_binder` that keeps the type test as a **fallback**, so a lost attribute
degrades to today's behaviour rather than to a mismatch.

### Two bugs this found

* **`drop_spec_args` did not look deep enough.** It looked for binders in *one*
  `arrow_formals` of the head's type, unfolding once if that produced too few.
  That is not enough when the `squash` binder is inside the head type's
  **result**: for `callee : t_t -> Tot t_t` where
  `t_t = x:int -> y:int -> Pure r (requires ...)`, the visible arity is 1 and
  one unfolding of the whole type still exposes only the outer arrow. The `()`
  proof then survived into the generated OCaml and the ML typechecker rejected
  it with Error 76, "Ill-typed application". It now unfolds the *result* of the
  arrow it found, repeatedly, until it has as many formals as there are
  arguments — bounded by fuel and by the unfolding reaching a fixpoint.
* **`formals_of` walked the *declared* type of the head.** For
  `identity #(x:int -> Pure int (requires x >= 0) (ensures fun _ -> True)) f 1 ()`
  it saw `identity`'s own `[#a; x]` and never the `#(squash (x >= 0))` binder
  that appears only once `a` is instantiated. It now substitutes the arguments
  it has already consumed into the result type before unfolding it, so the
  *instantiated* arrow is what gets walked.

---

## 11. Resugaring, printing and error messages

The resugarer folds `#(squash P) -> Tot (x:t{Q x})` back into
`Lemma (requires P) (ensures Q)`, using `source_effect_name` to recover the name
the user wrote. Error messages and IDE hovers therefore read as before, and
squash binders print as *hypotheses* rather than as arguments.

`Syntax.Util.post_of_result_typ` is the partial inverse of `refine_with_post`
and is what recovers `fun x -> Q x` from `x:t{Q x}` or `squash Q`. Use it rather
than pattern-matching on a refinement by hand; it returns the trivial
postcondition when there is nothing to recover.

`comp_source_effect_name` and `combine_source_effect_name` (which decides which
written name a `bind` or a lift inherits) are in `Syntax.Util`.

A failed `()`-against-`squash` check now reports **"Assertion failed"** rather
than "Subtyping check failed" — the obligation really is an assertion now.

---

## 12. Migration and idioms

This section is the practical residue of verifying ulib, Pulse, `examples`,
`doc`, and three large external codebases (EverParse, kuiper, pulse-verified-gc)
against the change. The recurring root causes are just **two**:

* **A specification is now part of a type, so it participates in unification.**
  `Lemma (ensures Q)` used to be `unit`-returning with `Q` in the comp; it is
  now `Tot (squash Q)`. Passing such a proof where `squash (... ?u ...)` is
  expected therefore *solves* `?u` from the lemma's statement, where previously
  the unifier saw only `unit` and left `?u` to the expected result type.
* **`Pure`/`Ghost` with an `ensures` returns a refined type.**
  `val v (x:t) : Pure nat (ensures fun y -> fits y)` used to have result type
  `nat`; it now has `y:nat{fits y}`. Any implicit solved from such a result
  picks up the refinement.

### Surface-syntax changes

* `effect M = N` is canonical; the eta-expanded `effect M (a:Type) = N a` is
  accepted; anything else is Error 316.
* `effect M = N <: ...` (`redefine_effect`) is gone.
* The `[attributes ...]` clause on an effect declaration is gone.
* `sub_effect` must name effects, not abbreviations: `sub_effect Tot ~> M`.
* A universe application on an effect (`Tot u#0 int`) is rejected.
* `introduce` and `eliminate` no longer bind a name for the hypothesis: write
  `with e`, not `with h. e`. The hypothesis is an implicit `squash` binder that
  F\* puts in the proof context of `e` itself, so there is nothing to name. The
  old form is rejected with a message saying so.
* `assume_safe`'s argument is now `squash False -> Tac a`, not `unit -> Tac a`.
  Write `assume_safe (fun _ -> ...)`.
* `apply` now works on lemmas; `pose_lemma` is joined by `pose_apply`.
* `--ext optimize_let_vc` is inert; existing flags in downstream Makefiles need
  no change.

### `Classical.move_requires`

`move_requires` no longer *applies* to a lemma with no `requires` — and no
longer needs to. Such a lemma has no `squash` binder to move, so it has one
binder fewer than `move_requires` expects. The gap is bridged by
`try_eta_expand_to_expected_typ` ([§6.3](#63-eta-expansion-across-an-arity-mismatch)),
so the idiom keeps working, but the wrapper is not *wanted*: `Lemma (ensures Q)`
is literally `Tot (squash Q)`, which is exactly what `Classical.forall_intro*`
expects, so pass the lemma directly.

### Accepted regressions, and the idiom for each

| Symptom | Remedy |
|---|---|
| A precondition failure is localized to a let-bound alias rather than to the call. | — (accepted) |
| An implicit solved from a `Pure`/`Ghost` result picks up its refinement (`SZ.v n == cap` demands `fits cap`). | Ascribe: `(SZ.v n <: nat) == cap`, or give the implicit explicitly. `Prims.eq2` already carries `[@@@unrefine]`; promoting it from `--ext __unrefine` to the default is a proposed follow-up. |
| `Ghost.hide (cbor_map_sub m s)` infers `Ghost.hide`'s implicit at the *refined* result, giving `erased (m:cbor_map{...})`. | `Ghost.hide #cbor_map (...)`. |
| A point-free definition more general than its interface fails (arity gap). | Usually fixed by eta-expansion in subtyping; when the surplus binders are not implicit, or the comp is not pure/ghost, write it out: `(fun a b -> a + b)` for `( + )`. |
| An implicit is pinned by a *later* argument before an earlier constraint is processed (`solve_flex_rigid_meet` fires with one bound in hand). | Instantiate the implicit explicitly at the call site. |
| A `match`/`if` scrutinee's refinement is not available in the branches. | Bind the scrutinee with an explicit refined annotation. |
| In a chain of *nested* calls with refined results, only the outermost refinement is attached. | Let-bind each intermediate operand. |
| `assert` elaborates `==` at the *refined* type of its operands, adding a side condition. | Ascribe an operand at the intended type. |
| A module-local alias of an imported definition is not SMT-unfoldable to it when the interface has a `val` for the alias. | `assert_norm` the equation. |
| `coerce_eq () x` infers its source type from `x`, i.e. the refined one. | Ascribe the argument: `coerce_eq () (e <: intended_type)`. |
| A proof near the solver's limit tips over, because every lemma called in a Pulse block leaves its postcondition — now a refinement — in scope. | State the obligation as a small standalone lemma whose context contains only what it needs. Usually *faster* than before. |
| A lemma stated point-free over a function that has a `requires` is eta-expanded at each use, and two eta-expansions are two distinct closures to the solver. | Replace the `requires` with a refinement on the argument's own type. |
| The proposition a `squash`-typed *argument* proves is not published to the enclosing goal, so `coerce_eq (_ by tac) x` leaves the solver unable to relate the two types. | State the equation once, with the same tactic, before the use: `assert (a == b) by tac`. |
| A definition's precondition is a predicate over a scrutinee the body then `match`es, and the branch cannot see what it says about the branch's pattern variables. | Restate the consequence with a `Lemma` taking the precondition, called with `[@@inline_let] let _ = ... in` at the head of the branch. |
| `let x = assert p` at top level now has type `squash p`, so `p` becomes a fact for the rest of the module. | Ascribe `: unit` where that is not wanted — in particular `let _ : unit = assert False`, which otherwise poisons everything after it. |
| `assert`s discharged inside a `squash (...)` argument no longer contribute to the enclosing definition's own refinement. | Hoist the lemma call out of the `squash`. |
| `apply (\`magic)` fills in `magic`'s anonymous `unit` argument itself. | Drop the following `exact (\`())`. |
| `fail` returns a refined `unit`, so an unannotated tactic ending in `match ... \| [] -> fail ...` infers a refined result type. | Annotate `: Tac unit`. |
| `lemma_from_squash`-style fallbacks now match *every* squashed goal. | Remove the fallback; plain `intro` handles the goal directly. |
| The expected type of a `dtuple2` component is not pushed into an unannotated lambda, so the lambda lacks the implicit binder the `requires` desugars to. | Annotate the component. (A genuine inference gap; candidate follow-up.) |
| `let x : t = e` is genuinely lossy where it used to be free: an `ensures` is a refinement now, so an annotation naming the unrefined type throws away facts. | Remove the annotation, or refine it. Note this cuts *both* ways — some sites needed an annotation *added* (`{ PostHint? ph }`), because a `match` whose branches differ in their refinements joins to something weaker than the continuation needs. |

### Two rules of thumb

* **If a lemma's arguments are refined and its conclusion uses each of them
  under a partial operation, prefer a `requires`.** The `requires` path scopes
  its obligations; the refinement path produces one guard per use.
  `a /. b *. c /. d == a /. d *. c /. b` over `real{_ =!= 0.0R}` takes 0.30s
  with a `requires` and 11.1s with refinements, at the same budget.
* **When a trivial arithmetic fact times out inside a large proof, hoist it to a
  top-level lemma proved in an empty context.** It is the *context* that is
  expensive, not the goal. In pulse-verified-gc this pattern accounted for most
  of the fixes; one such hoist took a module from "canceled at rlimit 120" to a
  maximum used rlimit of 7.1.

---

## 13. Known limitations and open bugs

### 13.1 Obligations escaping a `let`

`Rel.try_solve_single_valued_implicits` solves any `unit`- or `squash`-typed
implicit with `()` unconditionally and defers the proof to
`check_implicit_solution_and_discharge_guard`, which re-typechecks the solution
under `{env with gamma = imp_uvar.ctx_uvar_gamma}` and discharges the guard
*there*. `gamma` carries binder sorts and nothing else — no let-equations, no
branch hypotheses. So an obligation raised by a precondition can be discharged
in a context that has lost the very equation that proves it:

```fstar
assume val h (x: nat { x > 129 }) : nat
assume val lemA (y1: nat) (q1: squash (y1 == y1)) : Lemma (ensures True)
let a1 (n: nat) : Tot unit = let m : nat = n + 130 in lemA (h m) (_ by (trefl ()))
```

fails with `Failed to prove: m > 129`, in a context that binds `m` but not
`m == n + 130`. An *annotated* inner let is what loses it: `check_inner_let`
takes `x.sort` from `U.comp_result c1`, and the annotation has already forced
that through `weaken_result_typ`, discarding the refinement that
`maybe_assume_result_eq_pure_term` would otherwise have attached.

Workarounds: drop the annotation; write `let m : (q:nat{q == n + 130}) = ...`;
or assert the equation (`assert` is a `let _ : squash p`, which puts `p` in a
binder sort).

Pre-existing, but far easier to hit now, because *every* precondition takes this
path. Left open on purpose: enriching an annotated let's binder sort would
change the SMT encoding of every annotated inner let in every F\* program.

### 13.2 A `squash p` binder is a weak SMT hypothesis

`Prims.squash p` *is* `_:unit{p}`, but the encoder treats the two spellings
differently. A refinement type gets a `refinement_interpretation` axiom, so a
hypothesis `HasTypeFuel f x _:unit{p}` yields `Valid p` in one E-matching step.
`Prims.squash p` is an application of an uninterpreted symbol, so reaching
`Valid p` requires first rewriting with `equation_Prims.squash` and then
matching the refinement axiom *up to congruence*. On small goals it manages; on
large ones it sometimes does not, and the hypothesis is then silently useless.

```fstar
val f (x1 x2: t) (_: squash (s x1 == s x2)) : ...   // p not available
val f (x1 x2: t) (_: (u:unit{s x1 == s x2})) : ...  // p available
```

Not new — upstream fails identically on a hand-written `squash` binder — but it
was rare, because upstream rarely *produces* one. The sharpest form is not a
precondition at all but a *typing* hypothesis: with `yh` declared at
`dsum_type t`, a leftover `squash (has_type yh (dsum_cases t tg))` leaves the
solver unable to see that `serialize ... yh` is a `Seq.seq`, and so unable to
prove `Seq.length (serialize ... yh) >= 0`.

Workarounds all amount to putting the fact into a *binder's type*, where the
refinement interpretation reaches it:

```fstar
val g (l: list a { pre l }) : ...    // instead of (l: list a) : Pure _ (requires pre l) _

let seq_length_nonneg (#a: Type) (s: Seq.seq a) : Lemma (Seq.length s >= 0) = ()
```

**Four fixes were tried in the encoder and all four were rejected**, because
each traded this rare failure for a different one:

| Attempt | Effect |
|---|---|
| Rewrite `squash p` to the refinement it denotes, before encoding | Mints a fresh `Tm_refine_<hash>` symbol and three axioms per *distinct precondition shape*; timed out `CBOR.Spec.API.Format` |
| Emit `HasType e unit /\ p` for a squash binder guard | Makes the equation available *eagerly*, merging E-graph classes before the relevant patterns fire; broke `LowParse.Spec.Base.serializer_injective` |
| A global axiom `HasTypeFuel f x (Prims.squash p) ==> Valid p` | Fires on *every* squash-typed hypothesis, including record fields holding pattern-less quantified laws; broke `FStar.Tactics.CanonMonoid` and `FStar.Algebra.CommMonoid.Fold.Nested` |
| Close the query over a `squash p` binding as `p ==> q` rather than `forall (x: squash p). q` | Exactly upstream's shape, and it does put `p` in the hypothesis set — but it fixed neither known failure while restating every precondition in every query |

Closing this properly means making the hypothesis available **lazily**, in a way
that does not also strengthen unrelated squash-typed hypotheses.

### 13.3 A postcondition can take two instantiations, behind a guard

The same weakness from the other end. Upstream, an application of a partial
function inside a specification published its postcondition as a ground fact,
because VC generation for the enclosing `bind` restated it. Now `mul` is a `Tot`
function with a refined result type and an implicit `squash` argument, so the
equation `v (mul a b) == v a * v b` is not stated anywhere; the solver must
*derive* it, from `typing_FStar.SizeT.mul` — which yields
`HasType (mul x y u) (Tm_refine_c477 x y)`, guarded by
`HasType u (Prims.squash (fits (v x * v y)))` — and then
`refinement_interpretation_Tm_refine_c477`. Two instantiations, the first behind
a `squash`-typed guard.

Editing the axioms of a failing goal directly separates the two costs:

| The equation is available as… | Result |
|---|---|
| status quo: `typing_` + `refinement_interpretation`, `squash` guard | `unknown` in 2.8s |
| one axiom patterned on `(mul x y u)`, `squash` guard | `unknown` in 2.8s |
| `typing_` + `refinement_interpretation`, guard rewritten to `Valid (fits …)` | `unknown` in 2.6s |
| **one axiom patterned on `(mul x y u)`, guard `Valid (fits …)`** | **`unsat` in 0.6s** |
| **one axiom, no guard at all** | **`unsat` in 0.6s** |

Both costs are load-bearing: neither halving the instantiation depth nor fixing
the guard is enough alone. Raising the rlimit does not substitute for either
(20M gives `unknown` after 93s; 100M was still running after ten minutes), nor
do `smt.arith.nl false`, `arith.solver 2`, `relevancy 0`, `case_split 0|1`, four
random seeds, or `--fuel 2 --ifuel 2 --z3rlimit 80`.

The clean fix follows directly: emit, for `val f : bs -> Tot (r:t{phi})`, an
axiom `forall bs. {:pattern (f bs)} guards ==> phi[f bs/r]`, with a squash
binder's guard given as `Valid p`. That is one new axiom per function with a
refined result — measurably not free — and its second half is the very rewrite
that broke `serializer_injective` above. Same trade-off, same treatment: it
wants its own change and its own measurement.

Downstream, the workaround is to say it in unrefined arithmetic, or supply the
equation with an `SMTPat` lemma.

### 13.4 The content of a proof argument is not restated

A tactic-solved `squash`-typed implicit proves a proposition that the enclosing
goal never sees. Upstream restated a bound term's type at every `bind`, so a
coercion's proof obligation was *also* published as a fact; `captured_typing`
restates only what a binder's elimination would lose, and a tactic-solved
implicit is not that.

This is diagnostically counter-intuitive, which is why it is worth recording:
for `CDDL.Pulse.Parse.MapGroup.impl_zero_copy_map_zero_or_more_aux`, the goal
term and the hypothesis list were byte-identical to upstream's, the axiom sets
emitted for every symbol involved were identical, and the proof still failed.
The difference was a single extra ground fact — an equation between two arrow
types, which are different `Tm_arrow_<hash>` symbols in the encoding (the domain
is inside the abstraction, not an argument to it), so no amount of congruence on
their domains relates them.

The workaround is to state the equation the coercion rests on, once, with the
same tactic:

```fstar
assert ((tvalue -> bool) == (dfst (Iterator.mk_spec r2) -> bool))
  by (norm [delta_only [`%dfst; `%Mkdtuple2?._1; `%Iterator.mk_spec]; iota; primops]; trefl ());
```

### 13.5 `Positivity.fst`'s `neg_match`

`tests/micro-benchmarks/Positivity.fst`'s `neg_match` raises a spurious Error 19
on a definition that is rejected anyway. When a *closed* scrutinee makes
`subst_pat_bvs_in_res_typ` fire and a branch builds an arrow, the branch must
transport its result type across `t == Some?.v g` — and F\*'s SMT encoding gives
arrow types no congruence, since each arrow is encoded as its own constant. This
is unprovable on the pre-refactor compiler too. Every parameterized form of the
same type-level match verifies.

### 13.6 `TestBV.fst`

`tests/tactics/TestBV.fst` is slow: **12.1s against 0.93s** before. The cause is
understood and is not new code.

`Rel.equal`, reached because the head is an interpreted symbol under an `EQ`
relation, normalizes both sides with `UnfoldUntil delta_constant`.
`FStar.UInt.logand` unfolds to `from_vec (logand_vec (to_vec a) (to_vec b))`,
and `to_vec` on a symbolic 64-bit argument builds an enormous term. The six
problems that take this path cost ~2s each and establish nothing: they are
`logand (v x) (v y) =?= logand (v y) (v x)`, i.e. commutativity — a semantic law
neither unfolding nor decomposition can establish.

Upstream, the same 41 interpreted-head problems arise, but every one still has a
unification variable on the right, so the `no_free_uvars t1 && no_free_uvars t2`
gate is false and `equal` is never called. Here the variables are solved by that
point — an improvement everywhere else and a pessimisation here.

**Two attempted fixes were withdrawn**, and the reasons generalise:

* *Skip the delta step when the heads are the same symbol and an argument still
  mentions a free variable.* Wrong twice over. `Env.is_interpreted` answers true
  for every fvar whose delta depth is `Delta_equational_at_level`, i.e. for
  *every ordinary let-definition* — so the skip applied to a broad class of
  equations. And "both sides unfold in lockstep so only the arguments can decide
  it" is false whenever the definition is a wrapper returning one of its own
  arguments: for `let natlt_coerce #m #n (i: natlt n { i < m }) : natlt m = i`,
  `natlt_coerce (natlt_coerce i) =?= natlt_coerce i` is settled at once by
  unfolding, while decomposing leaves `natlt_coerce i =?= i`, which
  `rigid_rigid_delta` fails on. Two kuiper modules stopped verifying.
* *Decompose first, fall back to `equal` only on failure.* Worse: `TestBV` went
  to **17.4s**, because a problem decomposes into subproblems and the expensive
  normalization then runs at every level before anything fails.

There is no cheap syntactic discriminator: both cases are a fully-matching head
applied to non-ground, reducible arguments, and what separates them is whether
the normalization pays off, which is only knowable by running it. Two plausible
real fixes, neither attempted: give the normalizer a step budget in this call,
or recognise that the two argument lists are a permutation of one another.

(Note also that the gate's comment claims `no_free_uvars` means "neither term
has any free variables", while it only inspects unification variables and
universes.)

### 13.7 Unbounded normalisation in `Rel.equal`

`Env.step` has no fuel constructor, so bounding the normalisation inside
`Rel`'s local `equal` helper is not a one-line change. It is the more
fundamental problem behind both §13.6 and the 32 GB divergence described in
[§6.5](#65-other-typechecker-fixes-carried-by-this-work).

---

## 14. Notes for compiler developers

### 14.1 `.checked` files are not tied to the compiler that produced them

`CheckedFiles` validates a `.checked` file against its source digest and
`cache_version_number` — and **nothing else**. A compiler change that does not
change source text is therefore invisible to every module whose artifact is
already on disk.

This is a correctness hazard, not only a measurement one. `.checked` payloads
are OCaml `Marshal`ed, so removing a constructor shifts every later tag, and a
stale artifact **segfaults** the compiler rather than failing to load.
**Bumping `cache_version_number` (`src/fstar/FStarC.CheckedFiles.fst`) is
mandatory** for any change to the shape of the marshalled syntax. This work
bumped it twice: once for the `comp'` collapse, once for shrinking `cflag`.

The first honest re-verification of the whole tree after that bump immediately
surfaced four real typechecker bugs that had been masked for the entire
refactor — the postcondition/continuation bug, the flex-with-two-bounds bug, the
top-level-type bug, and the `tc_pat` `id` bug, all listed in
[§6.5](#65-other-typechecker-fixes-carried-by-this-work). Three of them are
latent upstream.

### 14.2 What to wipe, and when

After a change to **compiler semantics**:

```bash
make 1 -j$(nproc)
rm -rf stage2/{fstarc,tests,ulib}.checked
find tests pulse doc examples -type d \( -name '_output' -o -name '_cache' \) -prune -exec rm -rf {} +
find tests pulse doc examples -name '.depend*' -delete
make ci -j$(nproc)
```

Points that have each cost a debugging session:

* **Test `.checked` files live in `_cache` as well as `_output`.** Wiping only
  the latter is what let several failures hide.
* **`stage3/{ulib,fstarc}.checked` are git-tracked symlinks into `stage2/`.**
  Never `rm -rf` them; wipe `stage2/ulib.checked` instead.
* **A stale `stage1/out/bin/fstar.exe` is enough to hide a bug.** `.checked`
  files do not depend on the compiler binary, so if stage 1 is not rebuilt,
  stage 2's `fstarc.checked` is never regenerated and the new compiler never
  typechecks the compiler's own sources. ulib and the test suite do exercise it;
  `src/` does not. Confirm with
  `find stage2/fstarc.checked ! -newermt <start of the run>`, which should come
  back empty.
* **A change to `FStarC.SMTEncoding.*` needs `ulib.checked` deleted** to have
  any effect at all ([§8.3](#83-checked-files-cache-the-smt-encoding)).
* Do not run a downstream build (EverParse, kuiper, …) concurrently with a
  `make ci` that is wiping `stage2/ulib.checked`; it fails with Error 317.

For fast single-module ulib iteration (~8s rather than ~3min for `make 1`):

```bash
stage1/out/bin/fstar.exe --include ulib --already_cached ',*' \
  --cache_dir stage1/ulib.checked --cache_off <file>.fst
```

(one file at a time).

### 14.3 Two generations, and the stage0 bump

`src/` is only ever lax-checked, so the one hard bootstrap question was whether
the **fixed stage0 binary** could desugar a flipped `Prims`. It could not: the
compiler hardwires `Prims.GHOST` in `Env.is_erasable_effect`, which relies on
`GTot → GHOST` unfolding, so making `GTot` primitive would silently stop erasure
from firing.

So the flip could not land in one generation:

1. **Generation 1** (`0444fb29c6`) makes the compiler *name-agnostic* about
   which spelling `Prims` declares — one canonical classification of the pure,
   ghost and divergent effect classes, with every hardwired comparison routed
   through it. No behaviour change. Then `make bump-stage0` (`0cdb18b5a5`).
2. **Generation 2** flips `Prims` and removes specifications from `comp_typ`.

This is the general recipe for changing something stage0 depends on: make the
compiler tolerant first, bump stage0, then change the thing.

### 14.4 Diagnostic recipes

**Is a regression semantic, or is it gensym noise?** A proof passing with no
margin can be knocked over by a shifted fresh-name counter. Two ulib modules
failed after a `Rel.fst` change that could not possibly affect them; the two
`.smt2` files differed **only** in gensym'd universe variable numbering
(`uu___79` → `uu___83`), and replayed offline the old file gave zero `unknown`
and the new one exactly one, at the same goal.

1. Run both compilers with `--log_queries` (the file lands in the *cwd* as
   `queries-<Module>.smt2`).
2. `diff <(sed 's/uu___[0-9]*/UU/g;s/@x[0-9]*/@X/g' A) <(sed ... B)`. If the only
   remaining difference is the `; STATUS:` comment, the inputs are equivalent
   and the compiler change is not the cause.
3. Confirm by replaying each file with `z3 -smt2` and counting `^unknown`. F\*
   embeds the per-goal `(set-option :rlimit N)` in the logged file, so an
   offline replay is faithful.

The right response to that diagnosis is to fix the *proof*, not to revert the
compiler change.

**Why does this goal fail here and not there?** Take the unsat core from the
**working** build rather than diffing proof states:

```bash
{ echo '(set-option :produce-unsat-cores true)'
  sed -n "1,<line before the goal's check-sat>p" queries-M.smt2
  echo '(check-sat)'
  echo '(get-unsat-core)'
} > f.smt2 && z3 -smt2 f.smt2
```

The named hypotheses in the core tell you exactly which fact the failing build
is missing.

**Is a regression caused by `dedup_vc`?** `FSTAR_NO_DEDUP_VC=1`.

**Is a regression caused by *this* change, or by upstream drift?** Run an
A/B/**C**: the downstream tree's pinned baseline, your branch, and plain
`origin/master`. Anything that fails in tree C is not yours. (For
pulse-verified-gc this mattered: plain master verified 231 of the 241 modules
the pinned baseline did, including both of the two hardest failures the branch
hit.)

**An isolated module check is not evidence.** One pulse-verified-gc definition
took 0.1s and 0.34 rlimit units when its module was checked on its own, and
timed out at rlimit 20 in a full build of the same tree with the same dependency
`.checked` files. Confirm every fix with a clean rebuild.

**When a regression is about inference rather than proof, look at the inferred
type, not at the error.** The useful oracle for the `asn1_any_oid` failure in
[§6.5](#65-other-typechecker-fixes-carried-by-this-work) was

```fstar
let _ = assert True by (print (term_to_string (tc (cur_env ()) (`Mod.f))))
```

run under both compilers: a spurious `#_: Type ->` binder was present in one and
absent in the other, and that reduced a 3000-line module to a fifteen-line test
case. Note also that when a regression is about inference, the caches of the
*dependencies* have to be wiped too — a stale `.checked` for a dependency masked
both the symptom and, on the first attempt, the fix.

### 14.5 Measured costs

* **Solver time.** No aggregate regression. A from-scratch verification of
  ulib's 319 modules takes ~1m35s wall at `-j16`, or 13.2 CPU-minutes. Removing
  `lcomp` on its own took ulib from 1m35s / 13.2 CPU-min to 1m21s / 12.6.
  Fifteen rlimit adjustments across ulib, Pulse, `examples` and `doc`; eleven
  *other* `#push-options` bumps that had accumulated during development turned
  out to be unnecessary and were removed.
* **Benchmark outliers.** `Bug3800.fst` is faster than before (0.31s/84MB vs
  0.47s/94MB); `Quicksort.Base.fst` is 7.6s vs 7.7s (and was 14.4s before the
  same source fix was applied to both); `TestBV.fst` is the one unfixed
  regression ([§13.6](#136-testbvfst)).
* **Downstream diff.** EverParse: 32 files, +246/−102. kuiper: 27 files,
  +354/−48. pulse-verified-gc: 8 commits. All three are explicit implicit
  arguments, type ascriptions, `assert`s restating a fact the solver used to be
  handed, and a handful of small helper lemmas — plus, in each tree, a comment
  on each change explaining why it is there.

---

## 15. Regression test index

| Test | Pins |
|---|---|
| `tests/tactics/CompRoundTrip.fst` | both reflection round trips, by computation, across five comp shapes |
| `tests/bug-reports/closed/Bug2596b.fst` | a spliced lemma with `source_effect_name = Tot` is still encoded as an axiom |
| `tests/bug-reports/closed/Bug1370b.fst` | Error 316 for a non-alias effect abbreviation |
| `tests/micro-benchmarks/SimpleEffects_ReprUniverse.fst` | a total effect's universe comes from its `repr` |
| `tests/extraction/InstantiatedSpecArgs.fst` | `formals_of` instantiates the head's type before looking for spec args |
| `tests/extraction/SquashArgErasure.fst` | `drop_spec_args` unfolds the arrow's *result* |
| `tests/tactics/ExactObligation.fst` | `exact`'s proof obligation is appended, not prepended |
| `tests/micro-benchmarks/PostconditionDomain.fst` | a postcondition's binder annotation is checked |
| `tests/micro-benchmarks/NamedSquashBinder.fst` | `split_squash_binders` keeps a user's named binder |
| `tests/micro-benchmarks/QualifiedPrecondition.fst` | `comp_requires` resolves the name before calling it trivial |
| `tests/micro-benchmarks/ImplicitArrowDefensive.fst` | `try_solve_single_valued_implicits` normalizes in the opened scope (`--defensive error`) |
| `tests/micro-benchmarks/LetRecRefinedFunctionResult.fst` | a `let rec` returning a function keeps its `ensures` |
| `tests/bug-reports/closed/SquashSubtypingDivergence.fst` | both directions of `has_uvar_needing_congruence` |
| `tests/bug-reports/closed/MoveRequiresNoPrecondition.fst` | `move_requires` on a lemma with no `requires` |
| `tests/bug-reports/closed/Bug3210.fst` | `Meta_monadic` records the bare type (elaborated-term size) |
| `tests/bug-reports/closed/Bug3800.fst` | trivial-implication simplification in `simplify_vc` |
| `tests/bug-reports/closed/Bug3213b.fst` | `dedup_vc`'s one visible cost (two obligations, one message) |
| `pulse/test/LetInLemmaBinder.fst` | `TypeChecker.Core` tolerates an unannotated `let` inside a type |
| `tests/tactics/Makefile` (`BQual`, `Parsing`) | the incremental and non-incremental `tc_one_file` paths agree |
