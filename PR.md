# Make `Tot`/`GTot`/`Div` primitive, and move specifications out of computation types

This replaces the design in #4508 / #4510 (pushing an *expected postcondition*
through the typechecker). That approach kept the Hoare specification inside a
`comp_typ` and worked around the consequences; this one removes it from
`comp_typ` altogether, so the consequences do not arise.

118 commits, 331 files, `+10024 / −4170`. Of that, **328 files and
`+6966 / −4170` are code and tests**; the remainder is this document,
`regression_questions.md` (two accepted regressions worked out in detail) and
`revise_primitive_effects.md` (the original design brief, kept for the record —
where it and this document disagree, this document is what was built).

## The two representations that went away

F* had `PURE`/`GHOST`/`DIV` as primitive effects, with `Tot`/`GTot`/`Div` as
*abbreviations* of them — and, separately, dedicated `Total`/`GTotal`
constructors in `comp'` carrying `Prims.Tot`/`Prims.GTot`. One concept, three
representations, each with its own hardwired lident comparisons (~140 of them).

Independently, a `comp_typ` carried `comp_pre` and `comp_post`, so an arrow's
meaning was split between its binders and a specification buried in its
codomain. That split is the source of the "arrows compared without their
pre/post" bug class, and it is what forced the expected-postcondition machinery.

After this PR:

```fstar
(* ulib/Prims.fst, at the very beginning *)
total assume effect Tot
total assume effect GTot
assume sub_effect Tot ~> GTot
```

`Pure`, `Ghost` and `Dv` become ordinary front-end abbreviations that are
unfolded and desugared away before the typechecker ever sees them, and

```fstar
and comp_typ = {
  effect_name        : lident;   // always a *root* effect
  result_typ         : typ;
  flags              : list cflag;
  source_effect_name : lident;   // what the user wrote; presentation only
}
and comp' = | Comp of comp_typ
```

A computation type is now a label and a result type. Obligations live in
`guard_t`, where they were always meant to live. (`source_effect_name` carries
no meaning of its own — see "An effect abbreviation is a bare alias" below.)

`comp_univs` went with them. It was there to carry the universe instance of a
*polymonadic* effect's `wp`, and a computation type has no `wp` any more: every
one of its ~50 read sites either passed the list straight back to a `mk_Comp`
that reconstructed the same comp, or fed it to a `wp` combinator that no longer
exists. The universe of a comp is now recovered where it is needed, from
`result_typ`, which is the one place it was ever really recorded.

Removing it is what made the next simplification possible.

## `lcomp` is gone

`TypeChecker.Common.lcomp` was a computation type whose `comp` was behind a
thunk:

```fstar
type lcomp = {
  eff_name    : lident;
  res_typ     : typ;
  cflags      : list cflag;
  comp_thunk  : ref (either (unit -> ML (comp & guard_t)) comp);
}
```

It existed because building a `comp` used to be expensive — it meant composing
`wp`s — while the three fields callers usually wanted (the effect, the result
type, the flags) were cheap. So the expensive part was deferred, and forced only
if someone actually needed it.

After the flip those three fields *are* the whole of a `comp`. What is left of
an `lcomp` over a `comp` is one thing: a deferred `guard_t`. So the type is
replaced throughout the typechecker by the pair it had become —

| was | is |
|---|---|
| `lcomp` | `comp` |
| a function returning an `lcomp` with a deferred guard | a function returning `comp & guard_t` |
| `TcComm.lcomp_comp lc` | `lc, Env.trivial_guard` |
| `lcomp_with_binder` | `comp_with_binder = option bv & comp & guard_t` |

and 12 API functions (`mk_lcomp`, `apply_lcomp`, `lcomp_set_flags`,
`is_total_lcomp`, `residual_comp_of_lcomp`, …) collapse onto their `Syntax.Util`
counterparts on `comp`. Three more retire outright, having become the identity
after the flip: `TypeChecker.Util.weaken_precondition`, `should_not_inline_lc`
and `lcomp_has_trivial_postcondition`, together with `Normalize`'s four
`ghost_to_pure_*_lcomp` variants.

The one thing that needs care is that a thunk was forced *inside* the scope of
the binders its guard mentions. `TcUtil.bind` closes a continuation's guard over
the bound variable and weakens it with `x == e`; that used to happen to whatever
the continuation's thunk produced when `bind` forced it. So an eager rewrite has
to hand those obligations to `bind` explicitly rather than conjoin them into the
ambient guard — `tc_match` passes `bind_cases`' guard as `bind`'s continuation
guard, and `tc_eqn` weakens and closes each branch's obligations over the
pattern variables itself.

The resulting verification conditions are, if anything, cleaner: a chain of
forced thunks used to leave behind vacuous quantifiers like
`forall (base: nat). base == base ==> P`, which are simply absent now. ulib
verifies in 1m21s wall / 12.6 CPU-minutes at `-j16`, against 1m35s / 13.2 before.

Two `expect_failure` annotations change, both because error *recovery* got more
honest. `weaken_result_typ` used to record the expected type on the `lcomp`'s
`res_typ` field alone, leaving the `comp` inside the thunk with the type that had
just been rejected; the inconsistency then produced a second, spurious error.
`Bug655.fst` no longer reports a bogus "`GTot` and `STATE` cannot be composed"
after a subtyping failure, and `Bug3213.fst` reports both of its offending
arguments instead of one plus a cascade.

The `cflag` list went from five constructors to two. It was

```fstar
and cflag = TOTAL | MLEFFECT | LEMMA | SMTPAT of term | DECREASES of decreases_order
```

and it is now, in full:

```fstar
and cflag =
  | SMTPAT of term            (* the SMT patterns of a Lemma, as a list literal *)
  | DECREASES of decreases_order
```

`TOTAL`, `MLEFFECT` and `LEMMA` are all gone. Each was a *restatement of the
effect name*, which is now always reliable, so each had a reader that tested the
name anyway:

- `MLEFFECT` was set exactly when `effect_name` was already `FStar.All.ML`.
- `LEMMA` is now `source_effect_name = Prims.Lemma`, which is what
  `is_lemma_comp` and `is_smt_lemma` read.
- `TOTAL` is now `PC.is_pure_effect_lid (comp_effect_name c)`, which is the whole
  of `Syntax.Util.is_total_comp`.

The last one took two steps and is the reason the other two could go. `TOTAL` was
sprinkled on every `Tot`-named comp, residual comp and `bind` result, but it had
one use that was not redundant: it recorded that a comp's effect was an
*abbreviation* rooted at `Tot`, such as `Lemma` — something the effect name did
not say, and which `is_total_comp` has no env to look up. So it was first
narrowed to that single job, and only deleted once the desugarer began resolving
abbreviations away, making `effect_name` unconditionally a root effect. See "An
effect abbreviation is a bare alias" below.

Two things fell out of the narrowing: `TypeChecker.Util.weaken_flags` became
dead, and `mk_bind` lost its `flags` parameter along with the standing `TODO`
about `bind`'s flags being inconsistent with the comp it returns.

## Where the specification went

In the only two positions where a computation type may appear:

| Position | `E t (requires P) (ensures Q)` becomes |
|---|---|
| **Arrow codomain** | `... -> #(_ : squash P) -> E (x:t{Q x})` — the implicit binder goes **last**, so `P` may mention the explicit binders |
| **Ascription** | assert `P` here, and ascribe `E (x:t{Q x})` |

The precondition becomes a *proof argument*: the caller must supply it, F*
instantiates it by unification, and the obligation is raised at the call site
with the caller's hypotheses in scope. The postcondition becomes a refinement of
the result type, which is exactly what a caller learns.

Both are suppressed when trivial, so the overwhelming majority of code is
untouched.

### Lemma

`Lemma` is the unit-result instance of the same rule, and is no longer special:

```fstar
effect Lemma (a: Type) = Tot a
```

```
val f (bs) : Lemma (requires P) (ensures Q) [SMTPat pats]
  ==>  bs -> #(_ : squash P) -> Tot (squash Q)
       flags = [SMTPAT pats], source_effect_name = Prims.Lemma
```

Since `squash Q` *is* `_:unit{Q}`, this is the general rule at `t = unit`. Two
things fall out:

- **The post-thunking hack is gone.** `Lemma`'s postcondition was thunked
  precisely so the precondition could be assumed while checking the post's
  well-formedness (#57). With `#(_:squash P)` bound to the left of the codomain,
  `P` is in scope for free. `thunk_ens`, `unthunk` and `unthunk_lemma_post` are
  deleted.
- **`Tot (squash phi)` and `Lemma (ensures phi)` are now the same type**, so the
  bespoke subtyping rule for that pair is deleted too.

### The SMT encoding of a `Lemma` is unchanged

This was the main risk: ~5300 `Lemma` occurrences, ~1080 with `requires`. If
trigger selection or the quantified-binder set shifted, proofs would fail
diffusely and far from the cause.

It does not shift. The comp still records that the user wrote `Lemma`
(`source_effect_name`) and still carries its `SMTPAT` flag, and the post is
written with the `squash` fvar, so the encoder recovers everything
structurally: `pre` from the trailing squash-typed implicit binder,
`post` from the argument of `squash`, and the quantifier ranges over the **real**
binders only. For

```fstar
val lem (x:int) : Lemma (requires p x) (ensures q (f x)) [SMTPat (f x)]
```

the emitted axiom is

```smt2
(assert (! (forall ((@x0 Term))
  (! (implies (and (HasType @x0 Prims.int) (Valid (L.p @x0))) (Valid (L.q (L.f @x0))))
   :pattern ((L.f @x0)) :qid lemma_L.lem)) :named lemma_L.lem))
```

— byte-for-byte the shape emitted before. Verified across no-`requires`
lemmas, multi-binder lemmas with `SMTPatOr`, universe-polymorphic lemmas with
fuel instrumentation, and lemmas with a quantified `ensures`.

## An effect abbreviation is a bare alias

Before this PR an effect abbreviation could take binders and give its
right-hand side a specification:

```fstar
effect MyTot (a:Type) = Tot a (ensures fun _ -> False)
```

Neither could mean anything. A computation type supplies exactly one argument —
its result type — so every binder but the first was already dead, and once a
comp carries no specification the `ensures` above is silently dropped:
`x -> MyTot b` checks as `x -> Tot b`. (An earlier commit on this branch,
`7e71460e09`, *added* support for an `ensures` here; this reverses it. Making it
mean what it says would require refining the result type at every use site of
the abbreviation, and a `requires` would have to become an implicit binder on an
arrow the abbreviation does not have.)

The machinery keeping that shape alive was substantial: `Env.norm_eff_name`
(~50 call sites), `lookup_effect_abbrev`, `unfold_effect_abbrev`,
`TcEffect.tc_effect_abbrev`, `eff_decl.univs`/`binders`, and the `TOTAL` and
`LEMMA` comp flags, which existed only to record env-free facts about a
not-yet-unfolded abbreviation.

An abbreviation is now what it always was in substance: another name for an
effect. **`ToSyntax` resolves it away**, so `comp_typ.effect_name` is always a
root effect and the typechecker never unfolds anything. `comp_typ` gains
`source_effect_name`, which records the name the user wrote so that error
messages, IDE hovers, `Syntax.Resugar` and `inspect_comp` can still say `Lemma`,
`Tac` or `St`. It is presentation only, with one exception: `Lemma` roots at
`Tot`, so `U.is_lemma_comp`/`is_smt_lemma` — and hence whether
`SMTEncoding.Encode` emits a lemma's axiom — read it.

`Sig_effect_abbrev` shrinks to

```fstar
| Sig_effect_abbrev { lid : lident; root : lident }
```

kept only so that a module read from a `.checked` file can rebuild its `DsEnv`.

The canonical surface form is `effect M = N`. The eta-expanded spelling
`effect M (a:Type) = N a` is still accepted, because `ulib` has to stay
parseable by the bootstrap compiler in `stage0`; everything else is now rejected
(Error 316) rather than silently misinterpreted.
`tests/bug-reports/closed/Bug1370b.fst` pins down the accepted and refused
forms.

Two hand-built-syntax sites named an abbreviation where a root effect is
required, and only worked before because `norm_eff_name` cleaned up after them:
`Pulse.Extract.CompilerLib` (`DIV`, `PURE`) and `is_ml_comp` / the `fail_exp`
letbinding (`ML`).

Three neighbouring pieces of surface syntax go with it:

- **`redefine_effect`** (`effect M = N <: ...`) is gone from the grammar. It was
  the only other production for `NEW_EFFECT`.
- **The `[attributes ...]` clause** on an effect abbreviation or redefinition is
  gone — the `ATTRIBUTES` token, the production, the `Attributes` surface-AST
  node and the `cattributes` plumbing it fed in `ToSyntax`. The only flag it
  ever produced was `CPS`, which went away with Dijkstra Monads for Free
  (`7e468aa485`), leaving a match with nothing but a wildcard raising "Unknown
  attribute". Nothing in `ulib`, `examples`, `tests`, `doc` or `pulse` writes it.
- **A lift must now name effects, not abbreviations.** A lift is an edge of the
  effect lattice and an abbreviation is not a node of it; `sub_effect PURE ~> M`
  worked only because `ToSyntax` quietly resolved it first. Now that `PURE`,
  `GHOST` and `DIV` are abbreviations of `Tot`, `GTot` and `Div`, write the
  effect. The error message names the effect the abbreviation stands for, so the
  fix is in the message.

A fourth, from the same clean-up of how a computation type's arguments are read:
a **universe application on an effect**, as in `Tot u#0 int`, is now rejected
rather than accepted and dropped. A computation is an effect applied to its
result type, so its universe is that type's and there is nothing an annotation
could add. It was recorded in `comp_univs` before this series and has been
silently discarded since. The commit that does this (`7c9426d2c8`) also
introduces `sort_comp_args`, a single classifier for "which argument is the
result type, which the pre, which the post". `comp_requires` — which lifts a
precondition out of a codomain into an implicit binder — used to scan for an
index in a way that had to agree with `desugar_comp`'s own classification but
shared no code with it, so a definition could acquire a binder that its `val`
does not have; and `desugar_comp` classified twice. Both are now driven from
`sort_comp_args`, and `Lemma` is simply the effect that has no result type and
may carry SMT patterns.

## A total effect's universe comes from its representation

`TcUtil.universe_of_comp` decided the universe of `M t` by

```
if M is pure/ghost, or marked `total`, then u_res else u#0
```

which is unsound for any total effect whose `repr` does not preserve universes.
Given

```fstar
let repr (a:Type u#a) : Type u#(max a 1) = (t:Type u#0 & a)
total reifiable reflectable effect { M with { repr = ...; ... } }
```

`M bool` is inhabited by a `(t:Type u#0 & bool)`, so it belongs in `Type u#1`;
answering `u#0` let `unit -> M bool` pass as a `Type u#0` while really carrying a
`Type u#1` value — an embedding of `Type u#0` into `Type u#0`.

`FStarC.TypeChecker.Core.check_comp` already had this right: for a total effect
it built `repr t` and took *its* universe. The main typechecker and the core
checker disagreed, and the main one was wrong. They now share
`Env.effect_universe`.

Rather than re-derive the representation's universe at every arrow,
`TcEffect.tc_eff_decl` reads it off `repr` once, when the effect is declared, and
stores it in `eff_combinators.repr_universe` as the scheme

```
[u_a]. Type u#r     where    repr u#u_a a : Type u#r
```

so that instantiating it at the universe of a result type gives the universe of
the computation type. This is a function of `u_a` alone: `repr`'s codomain
universe is fixed by its type.

The rule cuts both ways. A `repr` that *lowers* the universe — say
`repr (a:Type u#a) : Type u#0 = bool` — makes `M t` smaller than `t`, where the
old rule wrongly reported `u_res`; `unit -> M (Type u#5)` is now correctly a
`Type u#0`.

Unchanged: a partial effect still answers `u#0`, since an arrow into one is not a
type of values (`unit -> Dv t : Type0` for any `t`); and `Tot`, `GTot` and any
other `total assume effect` have no representation to consult, so they still
answer with the universe of the result type.

**This bug is not one the surrounding refactor introduced** — `master` has the
same three lines — but it is one the refactor's own test effects walk straight
into. Nothing in ulib or pulse declares a total effect with a representation, so
nothing there moves. `tests/micro-benchmarks/SimpleEffects_ReprUniverse.fst`
pins it.

## The size of an elaborated term

A postcondition is now a refinement of the result type, and a result type is part
of the term. That is fine in the two places a specification is *written*, and it
was a serious problem in one place it is *inferred*.

`Meta_monadic` / `Meta_monadic_lift` annotate a monadic `let` or application with
its result type, as a hint for reification and extraction — `tc_term` drops the
type when it re-checks such a term, and extraction ignores it. Recording the
*inferred* type there meant recording a postcondition that embeds the very terms
it describes: the definiens of a pure let, the result of every branch of a match.
Effectful code binds at every step, so the copies nested, and the elaborated term
grew multiplicatively with the nesting depth. Reducing
`FStar.Tactics.Visit.visit_tm` over a term of size *n* took time exponential in
*n*: `tests/bug-reports/closed/Bug3210.fst` went from **0.52s to 1214s**, and
`FStar.Tactics.Visit.fst.checked` from 151KB to 546KB.

Recording the bare type (`5f60b4c352`) puts Bug3210 back to 0.57s, makes
`visit_tm` flat in the size of the visited term again, and brings the checked
file to 255KB. Before specifications moved into the result type this information
lived in the WP, which was never part of the term, so this restores the size
annotated terms used to have.

## Getting a variable out of a type

The other consequence of an inferred postcondition being part of the type: it
mentions the terms it is about, so it routinely mentions variables that are
about to go out of scope — a `let`-bound name, a `match` pattern variable, the
names of a `let rec`. Five commits converge on a single discipline here, and it
is worth reading them together.

- **Recover, don't drop** (`8f70eb8b3f`). An inferred refinement that mentions an
  escaping variable used to have the offending conjuncts deleted. Quantify the
  escaping variables *existentially* instead: they witness the existential
  themselves, so this is still a weakening, but simplification then applies the
  one-point rule and the fact survives. `_ == x` with `x : nat` used to leave
  nothing behind and now yields `_ >= 0`; `_ == f x /\ x == 3` is recovered as
  `_ == f 3`. The whole formula is closed at once rather than conjunct by
  conjunct: with `y` escaping, `x == y /\ y == z` is recovered as `x == z`, which
  closing separately would reduce to nothing. The quantified binders' sorts are
  normalized, since the one-point rule restates the eliminated binder's typing
  hypothesis and cannot see it through an abbreviation — that is what turns `nat`
  into `_ >= 0`.
- **Decline to introduce, for `let rec`** (`3557bce2d2`). For the names bound by
  a `let rec`, the recovery above says nothing: `exists (f: a -> b). _ == f n` is
  witnessed by any constant function, while putting a higher-order quantifier in
  every type derived from this one. So those conjuncts are not introduced in the
  first place. `env.rec_names` records the names bound by the `let rec` whose
  body is being checked, and the four points in `TypeChecker.Util` that would put
  a term in a type consult it: `should_return`, `bind_result_subst`, the
  pure-substitution branch of `eliminate_binder_from_typ`, and `captured_typing`.
- **One authority** (`4c798eb6f4`). `check_no_escape` is that authority, but it
  lived in `TcTerm`, out of `TypeChecker.Util`'s reach — so
  `eliminate_binder_from_typ` had a last case that returned its argument with `x`
  still free and relied on `TcTerm` to notice, breaking the contract its name
  states. Moving `check_no_escape` and `escape_cause` into `TypeChecker.Util`
  *deletes* logic: the case used to drop refinements with `U.unrefine` when that
  happened to suffice, and `check_no_escape` does better — it normalizes first,
  so it sees through `squash` and other abbreviations, closes what it can
  existentially, and discards conjunct by conjunct rather than wholesale.
- **Never substitute an impure term into a type** (`42f039a3c1`). That last
  resort used to substitute the bound term, which is exact for a pure or ghost
  term and wrong for an effectful one, which may diverge and need not produce the
  same value twice. Instrumenting the branch finds it reachable: one hit across
  ulib and the test suite, at `tests/extraction/Micro.fst` with `c1 = Div`, where
  it produced `squash (f11 (g11 x) == g11 x)` — a type mentioning a `Div`
  application, which no source program could write.
- **Split the driver** (`d62b4d6194`). `bind_maybe_capture` had grown to ~500
  lines conflating four jobs: closing the binder, deciding how much of what `e1`
  established is worth restating, simplifying degenerate binds, and building the
  composite result type together with the `x == e1` hypothesis. The driver is now
  34 lines. `composite_result_typ` is the sole authority on the result type, and
  its two ways of getting rid of the binder are separated: `bind_result_subst`
  substitutes `e1`, `eliminate_binder_from_typ` closes `x` existentially when it
  cannot. This is the type-side counterpart of the guard-side elimination, which
  quantifies instead — types are closed by substitution, formulas by
  quantification — and the two do not conflict: the substitution rewrites the
  result type, where `x` is not bound, while the `x == e1` equation goes on the
  guard under `Env.close_guard`, where `x` deliberately stays.

## Smaller compiler fixes carried by this branch

Several of these are latent on `master` and were surfaced, not caused, by the
refactor.

- **A failed precondition is reported at the call, not at the definition**
  (`dc401f3935`). `check_implicit_solution_and_discharge_guard` discharged the
  guard with whatever range the environment happened to carry when the implicit
  was finally resolved, which is typically the enclosing definition. The range is
  now the implicit's own introduction site. This matters directly for the
  `squash` implicits that preconditions desugar to.
- **The normalizer can now compute universes of types that mention local
  binders** (`a198fab809`). The normalizer tracks the local scope in its own
  closure environment and never extends `cfg.tcenv`, so a type read off a
  residual comp or a monadic lift annotation may mention variables `tcenv` has
  never heard of. That was harmless while computation types carried no logical
  content; now that a result type carries the postcondition, such a type
  routinely mentions the binders the postcondition talks about, and
  `reify_bind`/`reify_lift`'s calls to `universe_of` trip the defensive
  well-scopedness check (Bug3236, Error 290). The free variables are reintroduced
  from the sorts they already carry before asking for the universe; a universe is
  determined by sorts alone, so no result changes.
- **`has_type` was instantiated at `u#0` twice** (`691d7c8598`), with a standing
  `TODO`. Only `Rel.guard_of_prob` was still on that path, and the SMT encoder
  *does* encode universe arguments, so a formula about `x <: t` at any other
  universe was encoded against a symbol nothing else mentions. Both universes are
  now computed at that site and `mk_has_type` takes them.
- **A failed plugin reduction could corrupt the term** (`fc8dbb0d71`).
  `examples/native_tactics/Registers.List.Test` was OOM-killed in CI (34 GB and
  still climbing locally). When a native plugin cannot unembed its arguments —
  because they are still symbolic — `arrow_as_prim_step_N` falls back to a
  "shadow" application rebuilt from the arguments its generated wrapper handed
  it, which exclude the universes and leading type arguments the wrapper stripped
  off. The result is a strictly *partial* application of the same head: `sel #int
  r 1` comes back as `sel r 1`. `reduce_primops` accepted that as a reduction,
  after which the term could never reach the primitive step again — the plugin
  was silently disabled for that occurrence even once its arguments became
  concrete. Latent on `master`; the primitive-effect flip made it reachable.
- **A native tactic's `.cmxs` was never rebuilt** (`f31316706f`).
  `load_native_tactics` compiles a plugin's extracted `.ml` only when the `.cmxs`
  is *absent*; an existing one is dynlinked however old it is. After a compiler
  rebuild every test in that directory failed with Error 353 ("interface mismatch
  on `FStarC_TypeChecker_Util`") or an undefined symbol, and the only cure was to
  know to delete the objects by hand. The stamps already depend on `$(FSTAR_EXE)`,
  so the objects are dropped there now.
- **`--ext optimize_let_vc` is now inert** (`f8a8e05784`). Keeping a let-bound
  variable opaque in the VC — `forall x. x == e ==> phi` rather than `phi[e/x]` —
  is no longer optional, and there are no layered effects left in `bind` to
  accommodate. The key defaulted to true in `Options.Ext.defaults` and nothing in
  the tree set it to false, so the disjunct it guarded was constantly false; the
  flags still passed by pulse, examples and karamel become inert rather than
  wrong, and are left alone. Two neighbouring dead branches go with it
  (`is_layered` was the literal `false`; an `else` was unreachable because the
  guard of the case above it contains `not is_let_binding`).
- **Every `Tot`/`GTot` test goes through a `Parser.Const` predicate**
  (`8b19adb704`). Collapsing `Total`/`GTotal` into `Comp` turned every match on
  those constructors into an open-coded `lid_equals ct.effect_name
  PC.effect_Tot_lid` — 20-odd copies of the knowledge that generation 1 existed
  to remove. `is_tot_lid`, `is_gtot_lid` and `is_tot_or_gtot_lid` are deliberately
  distinct from the *class* predicates (`Pure` and `PURE` are in the pure class
  but are not `Tot`), and `Syntax.Util` gains `is_named_gtot` /
  `is_named_tot_or_gtot` so a caller holding a `comp` never reaches for the
  effect name. This found a latent inconsistency: `Normalize` gave a reified
  divergent let-binding `lbeff = Dv`.
- **A matching loop in `FStar.Rational.Gcd`** (`14351b8174`). The module header
  already warns that `is_gcd` and `divides` reliably produce matching loops with
  nonlinear arithmetic, and the module is written to keep them apart; one `assert`
  was proved with the recursive call's `is_gcd` postcondition in scope, and z3
  fired `primitive_Prims.op_Star` 22k times. Raising the rlimit does not help — it
  is a loop, not a marginal proof. Hoisting the arithmetic into a private lemma,
  where the `is_gcd` fact is not in scope, brings the module to 4.5s.

## Two generations, and a stage0 bump

`src/` is only ever lax-checked, so the sole hard bootstrap question is whether
the **fixed stage0 binary** can desugar a flipped `Prims`. It cannot: the
compiler hardwires `Prims.GHOST` in `Env.is_erasable_effect`, which relies on
`GTot → GHOST` unfolding, so making `GTot` primitive silently stops erasure from
firing.

So the flip could not land in one generation:

1. **Generation 1** (`0444fb29c6`) makes the compiler name-agnostic about which
   spelling `Prims` declares — one canonical classification of the pure, ghost
   and divergent effect classes, with every hardwired comparison routed through
   it. No behaviour change. Then `make bump-stage0` (`0cdb18b5a5`).
2. **Generation 2** flips `Prims` and removes specifications from `comp_typ`.

## A caching discovery worth reading

`CheckedFiles` validates a `.checked` file against its source digest and
`cache_version_number` — and **nothing ties it to the compiler that produced
it**. Every ulib, Pulse and test file whose source text had not changed kept
reusing its pre-refactor artifact, so every green run during this work was
partly vacuous.

Collapsing `Total`/`GTotal` forced the issue: `.checked` payloads are OCaml
`Marshal`ed, so removing a constructor shifts every later tag, and a stale
artifact *segfaults* the compiler rather than failing to load. Bumping
`cache_version_number` is therefore mandatory, and this branch does it twice
(97 → 99 against current `master`): once for the `comp'` collapse, once for
shrinking `cflag`. It bought the first honest
re-verification of the whole tree, which immediately surfaced four real bugs
that had been masked for the entire refactor:

- **A postcondition stopped reaching its continuation** when the bound variable
  did not occur in the continuation's result type, as in `hd :: f tl`.
- **A flex variable with a refined *and* an unrefined upper bound** was solved to
  their meet, making the refinement part of the variable's definition and then
  asking every *lower* bound to prove it at its own source position.
  `let y = match ... in lem y; y` is enough to hit it. Deferring is right — with
  the wrinkle that deferring a problem removes it from `wl.attempting`, hiding
  the very bound that motivated the deferral, so deferred problems must be
  counted as bounds too.
- **A top-level definition recorded its body's type, not its declared type**:
  `let my_int : Type = int` was recorded at `eqtype`. Keeping the sharper type is
  right *inside* a definition and wrong at its boundary, where it publishes an
  implementation detail as the signature — and defeats
  `FStar.Tactics.Parametricity`.
- **`tc_pat` emitted `FStar.Pervasives.id (proj x)`** for a pattern variable. Only
  beta-reduction runs before that term reaches the branch's result type, so the
  `id` survived and blocked the projector equation. An identity lambda
  beta-reduces away.

If you review one thing, review these four. They are ordinary typechecker bugs
that this refactor exposed rather than caused, and three of them are latent
today.

The same trap has a second mouth, worth knowing about before touching the SMT
encoding: a `.checked` file caches not only a module's typechecked declarations
but also **its SMT encoding** (`encode_modul_from_cache`). Since `.checked` files
are not tied to the compiler that produced them, a change to
`FStarC.SMTEncoding.*` has no effect at all on any module whose artifact is
already on disk — including all of ulib. Measuring such a change means deleting
`stage{1,2,3}/ulib.checked` (and `fstarc.checked`, or the rebuild fails with
Error 317), not just rebuilding the compiler.

A fifth bug surfaced the same way, in the driver rather than the typechecker.
`fstar.exe -c M.fst -o M.fst.checked` — how every `.checked` file in the tree is
built — consulted the cache to decide whether to load dependences *on the fly*,
even though `-o` makes `tc_one_file` recheck `M` from source no matter what the
cache holds. So a stale-but-valid `M.fst.checked` silently switched `M` to the
non-incremental path, which typechecks the module only after its whole
desugaring is finished — and finishing pops the module's `open`s off the scope
that tactics read out of the environment. `tests/tactics/BQual.fst` then printed
`Prims.int` for `int`, and `tests/tactics/Parsing.fst` could not resolve `+`.
Both passed from a clean tree and failed on the second build. The decision now
mirrors the one in `tc_one_file`, so a build no longer depends on what was
lying around before it started; `tests/tactics/Makefile` checks both files a
second time to pin the two paths together.

## Testing against EverParse

`ci` is not a big enough sample for a change this broad, so the branch was also
run against [EverParse](https://github.com/project-everest/everparse)'s `fstar2`
branch — two clean clones built side by side, one with EverParse's pinned
toolchain to establish that the tree is green to begin with, one with this
branch's `stage3` compiler. The pinned build reported zero errors, so every
failure in the other build is a genuine difference attributable to this PR.

The experiment ran to a green build over several rounds (`-k` only ever exposes
one layer of failures at a time, since dependents of a failing module are
skipped). It found four more typechecker bugs and one extraction bug, all fixed
here:

- **Subtyping could not eta-expand across an arity mismatch.** A precondition is
  a trailing implicit binder, so `Pure t (requires p)` has one binder more than
  `Tot t`. `tc_abs` inserts a missing implicit for a *lambda*, but a point-free
  term had no way to bridge the gap. `try_eta_expand_to_expected_typ` in
  `TypeChecker.Util` now handles **both** directions — the term's type having
  fewer binders than expected and having *more*, all of them implicit (which is
  where an *application* lands). `e` is applied to the shorter of the two
  arities' worth of arguments, taken from the term's own type — whose sorts are
  concrete, where the expected type's may still be uvars — while the
  abstraction binds *all* of the expected type's binders, since `tc_abs` only
  ever inserts *leading* implicits and the ones at issue are trailing.
  It has to run **before** the subtyping check, not only in its failure branch:
  relating `x:a -> Tot b` to `x:a -> #_:squash p -> Tot b` does not fail, it
  succeeds with an unprovable `has_type b (#_:squash p -> Tot b)` obligation. So
  `weaken_result_typ` tries it up front, on types that are already syntactically
  arrows (so the common case costs nothing), and again after subtyping has
  failed, that time normalizing first. Eta-expanding an effectful term would
  delay, duplicate or drop its effect, so both hooks are guarded by
  `is_pure_or_ghost_comp`. This closes the follow-up that the "point-free
  definition" regression below asked for.
- **A refinement was dropped when joining two lower bounds under unsolved
  universes.** Two structurally identical refinements can differ only in the
  universe uvar of an `eq2`; `U.term_eq` compares universe uvars by identity, so
  `combine_refinements` concluded the two bounds were genuinely different and
  widened to the base type, silently losing the refinement. It now falls back to
  `try_eq` **on the two refinement formulas** when `term_eq` says no. `try_eq`
  runs with `smt_ok=false`, so it can only unify structurally-equal formulas
  modulo universe solving — applying it to the whole types instead would wrongly
  identify `t` with `t{phi}`.
- **`TypeChecker.Core` rejected an unelaborated `let` inside a type.** Core's
  `Tm_let` case typechecked `lb.lbtyp` unconditionally, but a `let` that occurs
  inside a *type* — e.g. the binder sort `(x:nat) -> squash (let y = x + 1 in y > 0)`
  of a Pulse `fn` argument — can still carry the `Tm_unknown` the desugarer left
  there. Core then failed with `Unexpected term: Tm_unknown`. It now falls back
  to the definition's inferred type when the annotation is absent, which is
  sound: an unannotated `let`'s type *is* its definition's type, and the
  subtyping check it would otherwise perform is then reflexive.

  It is worth being precise about where that hole comes from, because "Pulse
  hands Core an unelaborated term" would be a much more alarming statement than
  what is actually happening. Pulse *does* elaborate binder sorts:
  `Pulse.Checker.Abs.arrow_of_abs` sends each one through
  `Pulse.Checker.Pure.tc_type_phase1`, which calls `tc_tot_or_gtot_term` with
  `phase1=true` and `admit=true`. That call sets `instantiate_imp`, and runs
  `solve_deferred_constraints` and `resolve_implicits` before returning, so
  implicit arguments *are* inserted and solved; `let y = id 0 in y >= 0` comes
  back fully applied. The one field phase 1 deliberately leaves blank is
  `lb.lbtyp`, and it is *this branch's own* phase-1 code that leaves it blank:
  `TcTerm.check_inner_let` keeps `lbtyp = tun` when the source had no annotation
  (see the comment there), because phase 1 discards specifications and phase 2
  reads `lbtyp` back as if it were a source annotation — recording phase 1's
  coarser type would throw away the postcondition, which is now a refinement on
  the result. So the hole is intentional, it is confined to that one field, and
  the two consumers of phase-1 output are phase 2, which re-infers it by design,
  and Pulse, which does not. Patching Pulse would mean asking it not to use
  phase-1 elaboration at all; tolerating a missing annotation in Core is both
  smaller and independently correct, since Core is a checker for arbitrary
  well-scoped terms and an unannotated `let` is one. Reached in practice only
  through Pulse; the original repro was a `fn` binder of `Lemma` type whose
  `ensures` contained a `let`. Regression test:
  `pulse/test/LetInLemmaBinder.fst`.
- **A `let rec` whose result is a function lost its `ensures`.** An `ensures` is
  now a refinement on the result type, so a definition returning a function is
  annotated with a *refinement of an arrow*. `Syntax.Util.arrow_formals_comp`
  deliberately looks *through* such a refinement to find the binders underneath,
  and throws the predicate away — harmless for a caller that only counts
  binders, fatal for one that rebuilds a type from what it got back. Two did:
  `TcUtil.extract_let_rec_annotation`, which moves the annotation onto the body
  and so was checking the body against the *unrefined* arrow, and
  `TcTerm.guard_letrecs`, which gives the recursive occurrence its type and so
  was hiding the definition's own postcondition from its recursive calls. The
  postcondition was then left to a single subtyping check on the whole
  definition, discharged with none of the body's facts in scope, and typically
  unprovable. `Normalize.get_n_binders_no_unrefine` splits with the strict
  splitter, falling back to the old one only when that finds too few binders, so
  it can never see less than before; the four sites in
  `extract_let_rec_annotation` and the one in `guard_letrecs` use it.
  Regression test: `tests/micro-benchmarks/LetRecRefinedFunctionResult.fst`.

- **Extraction left a precondition's proof argument behind.** A `requires` is a
  trailing implicit `squash` binder, and extraction erases it: `is_spec_binder`
  recognises it, `binders_as_ml_binders` drops it from a lambda and
  `drop_spec_args` drops the matching argument from an application. But
  `drop_spec_args` looked for the binders in *one* `arrow_formals` of the head's
  type, unfolding it once if that produced too few. 
  
  > NS: is_spec_binder seems too liberal. It will erase any implicit squash
  > argument, not just the ones that are inserted as the desugaring of requires
  > clauses. Can we add an attribute or something to the additional argument to
  > introduced by desugaring to indicate that only these are spec binders that
  > should be erased

  It is deliberately liberal, and the liberality is not observable. `squash p`
  is `x:unit{p}`, so an argument of that type carries no information whatever
  its provenance; erasing it can only ever be right. Concretely, a *use* of such
  a variable in the body extracts to `()` whether or not its binder was kept:

  ```fstar
  let h (#s : squash (1 == 1)) (x:int) : int & squash (1 == 1) = (x, s)
  let use () : int & squash (1 == 1) = h #() 3
  ```
  ```ocaml
  let h (x : Prims.int) : (Prims.int * unit) = (x, ())
  let use (uu___ : unit) : (Prims.int * unit) = h (Prims.of_int 3)
  ```

  and the higher-order case stays consistent because the *type* is erased by the
  same predicate: `#s:squash (1 == 1) -> int -> int` extracts to
  `Prims.int -> Prims.int`, so a lambda, an application, and a value of that
  type all agree.

  Attributing the desugarer's binder is a one-line change at `ToSyntax.fst:1337`
  — it is the only place an implicit `squash` *binder* is built — but it would
  make erasure depend on provenance rather than on type, and provenance is the
  thing that is easy to lose. Every path that rebuilds an arrow would have to
  preserve the attribute: `Syntax.Util`'s arrow constructors, Pulse's
  `Pulse_Extract_CompilerLib`, the reflection API's `mk_arrow`, and
  `TcUtil.extract_let_rec_annotation`, which already demonstrably drops a
  refinement it does not know about (see the `let rec` finding above). A single
  miss is silent: that one definition keeps the argument while its callers drop
  it, which is exactly the ABI inconsistency the type-directed predicate cannot
  produce. It would also need `cache_version_number` bumped, since a `val`
  checked before the change and a `let` checked after would disagree.

  So: not done, and not because it is hard. If the attribute is wanted anyway,
  the right form is a marker in `Prims` (a `requires` inside `Prims.fst` itself
  must be able to mention it) plus a check in `is_spec_binder` that keeps the
  type test as a *fallback*, so that a lost attribute degrades to today's
  behaviour rather than to a mismatch.


  That is not enough when the
  `squash` binder is inside the head type's **result**: for
  `callee : t_t -> Tot t_t` where `t_t = x:int -> y:int -> Pure r (requires ...)`,
  the visible arity is 1 and one unfolding of the whole type still exposes only
  the outer arrow. The `()` proof then survived into the generated OCaml as a
  real argument, and the ML typechecker rejected it with
  `Error 76: Ill-typed application`. `drop_spec_args` now unfolds the *result* of
  the arrow it found, repeatedly, until it has as many formals as there are
  arguments — bounded by fuel and by the unfolding reaching a fixpoint, so a type
  that genuinely has fewer binders than arguments still costs one step.
  Regression test: `tests/extraction/SquashArgErasure.fst`.
(A sixth problem, in the SMT encoding rather than the typechecker, was
root-caused but deliberately **not** fixed; see below.)

## An open bug: obligations escaping a `let`

`Rel.try_solve_single_valued_implicits` solves any `unit`- or `squash`-typed
implicit with `()` unconditionally and defers the proof to
`check_implicit_solution_and_discharge_guard`, which re-typechecks the solution
under `{env with gamma = imp_uvar.ctx_uvar_gamma}` and discharges the guard
*there*. `gamma` carries binder sorts and nothing else — no let-equations, no
branch hypotheses. So an obligation that a precondition raises can be discharged
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
`maybe_assume_result_eq_pure_term` would otherwise have attached. Dropping the
annotation, or writing `let m : (q:nat{q == n + 130}) = n + 130`, or asserting
the equation (`assert` is a `let _ : squash p`, which puts `p` in a binder sort)
all make it go through.

This is pre-existing, but this PR makes it far easier to hit, because *every*
precondition is now a `squash` implicit and so takes this path. It is left open
on purpose: enriching an annotated let's binder sort would change the SMT
encoding of every annotated inner let in every F* program, which is not a change
to make blind at the end of a refactor. The workarounds are local and cheap.

## A second open bug: a `squash p` binder is a weak SMT hypothesis

`Prims.squash p` *is* `_:unit{p}`, but the encoder treats the two spellings
differently. A refinement type gets a `refinement_interpretation` axiom, so a
hypothesis `HasTypeFuel f x _:unit{p}` yields `Valid p` in one E-matching step.
`Prims.squash p` is an application of an uninterpreted symbol, so reaching
`Valid p` obliges the solver to first rewrite with `equation_Prims.squash` and
then match the refinement axiom *up to congruence*. On small goals it manages;
on large ones it sometimes does not, and the hypothesis is then silently useless.
Side by side, at the same call site:

```fstar
val f (x1 x2: t) (_: squash (s x1 == s x2)) : ...   // p not available
val f (x1 x2: t) (_: (u:unit{s x1 == s x2})) : ...  // p available
```

This is not new — upstream F* fails identically on a hand-written `squash`
binder — but it was rare, because upstream rarely *produces* one. This PR makes
every precondition such a binder, so the weakness is now reachable from ordinary
code. Its sharpest form is not a precondition at all but a *typing* hypothesis.
Checking `serialize (serialize_dsum_cases t f sr g sg tg) yh`, where `yh` is
declared at `dsum_type t`, leaves `squash (has_type yh (dsum_cases t tg))` in
scope; the solver then cannot see that `serialize ... yh` is a `Seq.seq`, and so
cannot prove `Seq.length (serialize ... yh) >= 0` --- a goal that is true by the
result type of `Seq.length`. That is
`LowParse.PulseParse.Sum.l2r_safe_writer_dsum_noroom_lemma`, the one EverParse
definition that hits this.

The workarounds all amount to putting the fact back into a *binder's type*,
where the refinement interpretation reaches it:

```fstar
val g (l: list a { pre l }) : ...        // instead of  (l: list a) : Pure _ (requires pre l) _

let seq_length_nonneg (#a: Type) (s: Seq.seq a) : Lemma (Seq.length s >= 0) = ()
                                         // [s]'s own binder carries what the caller lost
```

Three ways to close it in the encoder were tried and all three were **rejected**,
because each traded this rare failure for a different one:

| Attempt | Effect |
| --- | --- |
| Rewrite `squash p` to the refinement it denotes, before encoding | Mints a fresh `Tm_refine_<hash>` symbol and three axioms per *distinct precondition shape*; timed out `CBOR.Spec.API.Format` |
| Emit `HasType e unit /\ p` for a squash binder guard | Makes the equation available *eagerly*, merging E-graph classes before the relevant patterns fire; broke `LowParse.Spec.Base.serializer_injective` |
| A global axiom `HasTypeFuel f x (Prims.squash p) ==> Valid p` | Fires on *every* squash-typed hypothesis, including record fields holding pattern-less quantified laws; broke `FStar.Tactics.CanonMonoid` and `FStar.Algebra.CommMonoid.Fold.Nested` in ulib |

Every variant is a net-neutral trade of one rare instability for another, so the
encoding is left alone. Closing this properly means making the hypothesis
available *lazily*, in a way that does not also strengthen unrelated
squash-typed hypotheses — a change to make on its own, with its own measurement,
not at the end of a refactor.

A fourth attempt was made and also rejected: closing the query over a
`squash p` binding as `p ==> q` rather than `forall (x: squash p). q`
(`Encode.encode_query`). That is exactly the shape upstream produces, and it does
put `p` in the solver's hypothesis set directly — but it fixed neither
`l2r_safe_writer_dsum_noroom_lemma` nor the `MapGroup` failure below, while
restating every precondition in every query. It was reverted.

## A third finding: the content of a proof argument is not restated

`CDDL.Pulse.Parse.MapGroup.impl_zero_copy_map_zero_or_more_aux` was the last
EverParse regression, and it is worth recording because the diagnosis is
counter-intuitive: the *goal term* and the *hypothesis list* are byte-identical
to upstream's, the axiom sets emitted for every symbol involved are identical,
and the proof still fails. The difference is a single extra ground fact.

The proof asserts

```fstar
assert (Ghost.reveal i.ser2 == coerce_eq (_ by (norm [...]; trefl ())) sp2.serializable)
```

where `i.ser2 : erased (dfst (mk_spec r2) -> bool)` and
`sp2.serializable : tvalue -> bool`. The two arrow types are *different*
`Tm_arrow_<hash>` symbols in the encoding — the domain is inside the abstraction,
not an argument to it — so no amount of congruence on `dfst (mk_spec r2) == tvalue`
relates them. The hypothesis in scope is `i.ser2 == hide (tvalue -> bool) sp2.serializable`,
and `lemma_FStar.Ghost.reveal_hide` triggers on `reveal a (hide a x)`: it can only
fire if the two `erased` type indices are the *same* E-graph term. So the proof
needs the equation between the two arrow types, and nothing else will do.

That equation is exactly the `squash (a == b)` argument the user's tactic solves.
Taking the unsat core of upstream's query names it directly (`@hypothesis_135`):
upstream restates a bound term's type at every `bind`, so the coercion's proof
obligation is *also* published as a fact. This branch's `captured_typing` restates
only what a binder's elimination would lose, and a tactic-solved implicit is not
that, so the fact is dropped.

The workaround is to state the equation the coercion rests on, once:

```fstar
assert ((tvalue -> bool) == (dfst (Iterator.mk_spec r2) -> bool))
  by (norm [delta_only [`%dfst; `%Mkdtuple2?._1; `%Iterator.mk_spec]; iota; primops]; trefl ());
```

which is the same tactic already written inline for the coercion. The definition
then verifies in 32s, against 45s for the failing attempt.

## Testing against kuiper

EverParse exercises parsing and low-level imperative code; it says little about
type-level computation, typeclasses, or Pulse's implicit-heavy style. So the
branch was run a second time, against
[kuiper](https://github.com/FStarLang/kuiper) at `c1cd3c2d`, using the same A/B
method: one clone built with the F* fork kuiper is developed against, one with
this branch merged with that fork (the merge is conflict-free and touches
nothing this PR touches). The baseline verifies all 396 modules with zero
errors, so again every difference is attributable to this PR. With the changes
below, the revised tree verifies all 396 modules too.

The interesting thing about kuiper is *where* it broke. EverParse's failures
were about specifications — an `ensures` that went missing, a precondition that
the solver could not use. Kuiper's were almost all about **unification**: a
`requires` is now a binder, so it changes the *shape* of types, and four
separate places in `Rel` turned out to handle refinements and proof-irrelevant
uvars in ways that only worked because those shapes did not arise before.

- **A typeclass-constrained variable was solved from an upper bound.** An
  instance head never mentions a refinement, so committing the variable to a
  refined upper bound makes the constraint unsolvable whatever the lower bounds
  say. Upstream had a rule preferring lower bounds for exactly this; generalising
  `prefer_lower_bounds` for the postcondition-as-refinement shapes had dropped
  it. Restored as a disjunct, so the `Bug026` case that motivated the extra
  conditions is unaffected. `Kuiper.Seq.Common.fsti`'s `seq_replace`, whose `++`
  is `Kuiper.Monoid`'s typeclass-dispatched `mplus`.
- **`refinement_of_flex` fired on a bound whose base is the variable being
  solved.** A recursive function with an implicit argument of inferred type —
  Pulse's `(#[full_default ()] f: _)` idiom — bounds that type by
  `x:?u (n-1) {decreases ...}`. Treating it as a head match makes `combine`
  build an equation that fails the occurs check; meet/join then gives up and the
  caller widens the bound all the way to its base, dropping the refinement the
  *other* bound asked for, so `perm` became `real`. Leaving it a `MisMatch`
  keeps the other bound intact. `Kuiper.SHMem.fsti`'s `live_c_shmems`.
- **Joining two lower bounds widened to a base neither side was written at.**
  `combine_refinements` widens to the base type when the joined predicate is
  neither input's — the right thing when the two bounds' bases were already the
  same type, since the disjunction of two refinements is rarely what a later
  upper bound needs. But when the bases agreed only *after* delta-unfolding —
  `natlt n1` and `natlt n2` both reducing to a refinement of `nat` — the base is
  a type neither side was written at, and widening to it throws away the very
  information the bounds carry: joining them to `i:nat{i < n1 \/ i < n2}` is what
  lets the result meet a later upper bound of `natlt (max n1 n2)`. The widening
  rule now applies only on the `try_eq` path, where the bases really were equal.
  `Kuiper.IView.fsti`'s `merge_either`, whose result was inferred at
  `-> GTot nat`. Regression test:
  `tests/micro-benchmarks/JoinRefinedLowerBounds.fst`.
- **A flex-flex problem at a proof-irrelevant type invented a uvar.**
  `solve_t_flex_flex`'s quasi-pattern rule allocates a fresh variable over the
  intersected binders and solves both sides to functions of it. When the shared
  result type is `squash phi` there is nothing to determine — `()` is its only
  inhabitant — and the fresh variable is simply never solved. This looked like a
  fifth bug for a while and it is *not*: the `Error 217` it produced came from an
  experiment elsewhere, and with that reverted the rule is unnecessary. Recorded
  here only because the shape is tempting: "solve both sides with `()`" also
  breaks `tests/tactics/SolvedWitness.fst`, whose whole point is that
  `assert True by (dup (); flip (); trefl (); qed ())` *does* leave a witness
  uninstantiated.
- **A goal that was open only in proof-irrelevant uvars was resolved too late.**
  `resolve_implicits'` defers a meta arg — a typeclass goal, in practice — whose
  type *or context* mentions a free uvar, on the grounds that solving something
  else may instantiate it (#3130). When nothing else can progress it gives up
  and runs the tactic on the open goals anyway, in the reverse of the order it
  first saw them, which is a much worse position to guess from. Since a
  `requires` now desugars to an implicit `squash` binder, uvars that carry no
  information at all are everywhere, and both halves of that test started
  misfiring:
  - By *type*: an otherwise ground goal like
    `has_pts_to (array2 et l) (frac (chest2 et (v (rows +^ 2sz)) d))` counts as
    open purely because of a `squash` uvar in one of its arguments.
    `Kuiper.Kernel.Stencil.fst`'s `kpre`.
  - By *context*: `Kuiper.Sparse.Common.fst`'s `is_ematrix_tile_at` is a
    `Pure prop (requires offset_chunk et j k nthr < cols)`, so its own `requires`
    binder is in scope while its body is checked — and the call it mentions has a
    `requires true` of its own, hence a `squash true` uvar. That single
    uninformative uvar makes `gamma_has_free_uvars` true, so *every* typeclass
    goal in the definition is deferred to the eager pass, where they are then
    attempted in dependency-violating order: `has_vec_cpy et #?s` runs before
    `?s : sized et` is solved, and instance search declines to guess `?s`.

  Before deciding whether a meta arg's goal is open, the loop now solves the
  single-valued uvars *of that goal and its context* — the same
  `()`-for-`squash phi` step the loop already performs, just targeted and
  earlier; their `phi` is still discharged when the loop reaches their own
  implicit. Restricting it to the goal's own uvars is load-bearing: running the
  general pass early instead re-broke `Kuiper.Seq.Common`, because solving
  unrelated single-valued implicits instantiated `monoid0 ?t` to the refined
  result type before instance search ever saw it. Regression test:
  `pulse/test/PtsToSquashImplicit.fst`.
- **`squash p <: squash q` was decided by equality, and diverged.** This is the
  most serious defect the branch had, and it is the one that a downstream
  campaign is uniquely good at finding: it needs no unusual feature, only a
  proposition whose proof term is expensive to unfold.

  `Lemma (ensures p)` is now `Tot (squash p)`, so a lemma whose body is itself a
  lemma call produces a subtyping problem between two *squashed propositions* —
  what the body proves against what the enclosing lemma promises. Upstream that
  problem did not exist: a lemma call had type `unit`, and the postcondition
  arrived as a guard from the computation type. Both sides now have head
  `Prims.squash`, so `head_matches` reported a match and the application
  congruence rule fired, decomposing the problem into `p == q` — an *equality*
  between the two propositions — and then delta-unfolding both of them looking
  for a syntactic match.

  For arithmetic propositions that merely wastes a little time. For bitvector
  propositions it does not terminate: `FStar.UInt.nth`, `logand` and
  `shift_right` unfold into `to_vec`/`from_vec` recursion, and the typechecker
  allocates until the machine dies. `Kuiper.Bitmask.fst` — 288 lines, 12s and
  under a gigabyte upstream — took a single `fstar.exe` past **561 GB** of
  resident memory before the kernel OOM-killer stopped it. It never once
  completed on this branch, and because the failure surfaced as a killed process
  rather than an error message it hid behind `make -k`'s exit status for several
  rounds.

  `squash p` is *by definition* `_:unit{p}`, so the two sides are related by
  implication, not equality. The fix makes `squash` transparent to subtyping:
  the problem is unfolded to its refinement form and handed to the existing
  `Tm_refine, Tm_refine` rule, which already knows to emit `p ==> q` — and
  already knows how to treat uvars in `p` and `q`, which is why the rewrite is
  delegated rather than open-coded. Gating it on both sides being uvar-free was
  tried first and does not fire: the `eq2` on the right of a typical `ensures`
  still carries an unresolved universe. Reduced to ten lines of ordinary F* in
  `tests/micro-benchmarks/SquashSubtypingDivergence.fst`; the fixed compiler
  checks it in 1.01s against master's 0.99s.

  Pulse reaches the same conclusion by a different route, and needed the same
  rule again in `FStarC.TypeChecker.Core`. There a `calc` justification has
  expected type `unit -> Tot (squash (p y z))`, the body has type `squash A`,
  and `check_relation'`'s `Tm_app`/`Tm_app` congruence demanded `A == B` via
  `check_relation_args … EQUALITY`. This one fails fast rather than diverging —
  it reports `A == true == B`, which is `eq2 (b2t A) B` printed — but it is the
  same confusion of proof irrelevance with syntactic identity.
  `Kuiper.Sparse.Matrix.PtsTo.fst` needed no downstream edit once it was fixed.
  Regression test: `pulse/test/CalcSquashSubtyping.fst`.

Downstream, kuiper needed **22 files, +99/-32 lines of code** (+260/-36 with the
explanatory comments each change now carries). Most are the familiar
kind — an explicit type ascription, a dropped `Classical.move_requires` that is
now redundant because the precondition is a binder, a calc justification
restated as the library lemma it was open-coding, a missing `lemma_divides_exact`
that the old encoding happened to supply anyway, and an arithmetic hint or an
`SMTPat` lemma where a `fits` obligation is no longer a ground fact (see the
fourth finding below). Six are more interesting:

- `Kuiper.Kernel.LogSoftmax.fsti`'s `log_softmax_real` had no result annotation,
  and its body sequences a `Lemma` call before returning. That postcondition is
  now a refinement on the `Lemma`'s `unit` result, and `captured_typing`
  propagates it onto the type of the `let`-body, so the *inferred* result type
  became `chest1 real n {forall i. acc (softmax_real ra) i >. 0.0R}`. No
  `can_approximate` instance head mentions a refinement, so downstream resolution
  failed. Annotating the result type is the fix. This is the most general
  downstream hazard in the PR: **an unannotated definition whose body sequences a
  `Lemma` now acquires a refined type**, which is usually harmless but is fatal
  to typeclass resolution.
- `Kuiper.Kernel.SDPA.Naive.fst`'s `scaled_add_approx` proved a
  `approx2 (fun x y -> ...) (fun x y -> ...)` goal with
  `introduce forall ... with introduce _ ==> _ with aux x y rx ry`, where the
  two `_`s of the implication are inferred from `aux`'s type — which is now
  `... -> #_:squash (x %~ rx /\ y %~ ry) -> Tot (_:unit{...})` rather than an
  arrow into `Lemma`. The two holes are left deferred and `tc_decl` reports
  `Error 54`. `Classical.forall_intro_4 (Classical.move_requires_4 aux)` proves
  the same thing in one line and does not depend on inferring them; the
  neighbouring `comb2_approx`, whose `approx2` arguments are named rather than
  lambdas, was unaffected. This one is a genuine inference regression rather
  than a design consequence, but it resisted a small reproduction, so it is
  recorded rather than fixed.
- `Kuiper.Example.ArrayView.Test.EvenOdds3.fst`'s `it_of_nat_lem_1` carries an
  `SMTPat` mentioning `it_of_nat vw i`, whose second argument is refined by
  `in_image vw.iview.step.imap.f i`. Upstream proves that refinement by
  brute-force unfolding — the baseline's unsat core names no lemma at all, just
  `merge_either`, `sum_aiview`, `even_view`, `odd_view` and friends. Here it must
  be said: `all_in_image`, which already existed twenty lines further down, moves
  *above* the two lemmas and loses its dependency on them, and the two lemmas
  take the fact as a `requires`. That is strictly better factored than what was
  there, but it is a real edit.
- `Kuiper.Tensor.Layout.Alg.fsti`'s `l4_batched_row_major_imap` states its
  right-hand side in `SZ.t` arithmetic, four `SZ.mul`s and three `SZ.add`s deep.
  Every one of them is partial, so the well-typedness of the *statement* is a
  `fits` obligation over the whole nest. It is now stated in `nat` arithmetic
  instead, which has no obligation at all. Why the original stopped working is
  worth recording precisely; see the next section.
- `Kuiper.Sparse.Load.fst`'s `load_cell` states its postcondition as
  `Cell (x <: array et) (SZ.v i) |-> Seq.index s j`. The `has_pts_to` instance
  is `has_pts_to (cell (array a) nat) a`, so the index type has to be literally
  `nat`; `SZ.v i` used to elaborate to exactly that, but its result type is now
  reached through `SizeT.v`'s refinement and comes out as `nat{fits …}`, which
  no instance head matches. Ascribing the index `(SZ.v i <: nat)` — kuiper's own
  idiom, e.g. `Kuiper.Kernel.HReduce.Block.Max.fst:374` — fixes it. This is the
  same hazard as `LogSoftmax` above, reached from the other direction: there a
  refinement was *added* to an inferred type, here one that was always there
  stopped being erased.
- `Kuiper.Sparse.SPMM.Compute.fst` needs the same fact as `block_lemma_off` at
  four separate places — `cnt` divides both `k` and `n` and `k < n`, so
  `k + cnt <= n` — once in a pure `Tot` function, once in a Pulse `fn`, once as
  a `fits` bound inside a `while` invariant, and once inside a `prop`
  *definition*, where there is no statement position to put a hint in. A local
  `__divides_next` lemma covers the first three. Giving it an `SMTPat` to cover
  the fourth is a trap: it discharges that goal but breaks an unrelated
  `decreases` check forty lines earlier, which is the usual cost of a pattern on
  a predicate as common as `divides`. Inside the `prop` the fact is scoped
  instead, `k2 < n ==> (let _ = __divides_next cnt k2 n in …)` — which works
  precisely because of this PR: sequencing a `Lemma` now puts its conclusion in
  scope as a binder rather than as an effect.
- `Kuiper.Sparse.SPMM.LoadSparse.fst` calls `forevery_rw_size` twice with the
  same equation, `v (n /^ nthr /^ chunk et) == v n / (v nthr * v chunk et)`,
  once before a `foreach` and once after. The first still goes through; the
  second, in the much larger context the `foreach` leaves behind, times out.
  `FStar.Math.Lemmas.division_multiplication_lemma` supplied explicitly fixes
  it. Both halves of the fourth finding are visible here at once: the `SizeT.div`
  equations are no longer ground, and what that costs depends on how much else
  is in the context.
- `Kuiper.Sparse.SPMM.Defs.fst`'s `block_lemma_off` proved
  `k * block + off < whole` by `()`, from `block /? whole`, `k * block < whole`
  and `off < block`. The lemma immediately above it, `block_lemma`, already
  states the missing step (`k * block + block <= whole`) and still proves by
  `()`; only the composite one needs it spelled out now. Calling it is the whole
  fix. Nothing here is about `squash`: it is a divisibility fact whose proof
  needs one nonlinear step, and the encoding change moved it across the
  threshold.

### Auditing the downstream changes, and what happened to the `z3rlimit` bumps

Every one of the 22 edits was re-tested individually, by restoring the original
text of just that change — in the multi-part files, of just that hunk — and
rechecking the module against the current compiler. All of them are still
required: none is left over from an intermediate state of the branch. The
harness is a scratch `--include` directory that shadows `src/`, so a single
module can be rechecked in about a minute against the already-built `obj`.

That audit also revised the three `z3rlimit` bumps, which are the changes most
likely to hide a future regression. **Two of the three are gone, and the
downstream diff now contains no rlimit increase at all** beyond one relocated
`#push-options "--z3rlimit 20"` that simply follows a moved lemma and matches
its two neighbours.

- `Kuiper.Math.OnlineSoftmax.fst`'s `abcd_adcb` — the fifth finding below — was
  carrying `--z3rlimit 30`. The real fix is to state the two non-zero side
  conditions as a `requires` instead of as refinements on `b` and `d`. Reduced
  to six lines over `FStar.Real` and nothing else, the refinement form takes
  **11.1s** and the `requires` form **0.30s**, both at the default rlimit; in
  the module itself the change replaces `--z3rlimit 30` and 22s with no option
  at all and 17s. The refinement form makes each of the four divisions in the
  conclusion re-derive its own guard, and those guards now survive into the
  goal's context, where nlsat case-splits every one of them; a single `requires`
  is one hypothesis instead.
- `Kuiper.Kernel.GEMM.SHMem.fst`'s `bkf` had been raised from 40 to 100. What
  actually fails is one `assert (pure (2 * (!bk + 1) == 2 * !bk + 1 + 1))` in
  the loop body — linear, trivial, and timing out only because of how much else
  is in scope by that point. Proving it as a two-line top-level lemma in an
  empty context and calling it instead **restores the original rlimit of 40**.
  (50, 60 and 80 all still fail without the lemma, so this was a real 2.5x bump,
  not a rounding-up.)
- `Kuiper.Kernel.GEMM.FlipFlopBarrier2.fst`'s `odd_barrier_p_to_q` is the one
  case where a raise is genuinely the right answer, and it is lowered from 100
  to 80. Here the failing goal is `it / 2 >= 0` with `it : natlt (2 * (shared/bk))`
  in scope. It is not a hint that is missing: asking for the fact as the very
  first `assert pure` of the body fails in 54s just as it does at the point of
  use, so the cost is the ambient VC — the function's slprops mention the
  concrete k-tile `it/2` where the neighbouring `even_barrier_p_to_q`, which
  needs no raise, uses an existential. A sequenced `Lemma` does not help either:
  it arrives at the query as a `Prims.unit` binder with its conclusion dropped.
  Measured, 20 and 40 fail while 60, 80 and 100 succeed, so 80 leaves a 2x
  margin over the last failing value without carrying the original number.

The two lemma-in-a-clean-context fixes above are worth generalising: when a
trivial arithmetic fact times out inside a large Pulse function, hoisting it to
a top-level lemma is almost always better than raising the budget, because it
is the context and not the goal that is expensive. It only fails when the
ambient VC is itself over budget, which is what distinguishes the
`FlipFlopBarrier2` case from the other two.

## A fourth finding: a postcondition now takes two instantiations, behind a guard

This is the same `squash p` weakness as above, seen from the other end, and
kuiper gives it a sharper measurement than EverParse did.

Upstream, an application of a partial function inside a specification publishes
its postcondition as a ground fact: `Pure` is a computation type, so VC
generation for the enclosing `bind` restates `v (mul a b) == v a * v b` for every
subterm. Here `mul` is a `Tot` function with a refined result type and an
implicit `squash` argument, so the equation is not stated anywhere; the solver
has to *derive* it, from `typing_FStar.SizeT.mul` (which yields
`HasType (mul x y u) (Tm_refine_c477 x y)`, guarded by
`HasType u (Prims.squash (fits (v x * v y)))`) and then
`refinement_interpretation_Tm_refine_c477`. Two instantiations, the first behind
a `squash`-typed guard.

Taking the failing goal — the `fits` obligation above — out of `--log_queries`
and editing the axioms directly separates the two costs:

| The equation is available as… | Result |
| --- | --- |
| status quo: `typing_` + `refinement_interpretation`, `squash` guard | `unknown` in 2.8s |
| one axiom patterned on `(mul x y u)`, `squash` guard | `unknown` in 2.8s |
| `typing_` + `refinement_interpretation`, guard rewritten to `Valid (fits …)` | `unknown` in 2.6s |
| **one axiom patterned on `(mul x y u)`, guard `Valid (fits …)`** | **`unsat` in 0.6s** |
| **one axiom, no guard at all** | **`unsat` in 0.6s** |

So *both* costs are load-bearing: the goal is provable, and neither halving the
instantiation depth nor fixing the guard is enough on its own. For completeness,
raising the rlimit does not substitute for either — 20M gives `unknown` after
93s, 100M was still running after ten minutes — nor do `smt.arith.nl false`,
`arith.solver 2`, `relevancy 0`, `case_split 0|1`, four random seeds, or
`--fuel 2 --ifuel 2 --z3rlimit 80` in the source. (`:produce-unsat-cores true`
*does* turn it `unsat`, which is a fact about z3's search, not about the goal.)

The clean fix follows directly: emit, for a `val f : bs -> Tot (r:t{phi})`, an
axiom `forall bs. {:pattern (f bs)} guards ==> phi[f bs/r]`, with a squash
binder's guard given as `Valid p` rather than `HasType u (squash p)`. That is
one new axiom per function with a refined result — measurably not free — and the
second half of it is the very rewrite that the table in the previous section
records as having broken `LowParse.Spec.Base.serializer_injective`. It is the
same trade-off, and it wants the same treatment: a change of its own, with its
own measurement across ulib, EverParse and kuiper, not a patch at the end of a
refactor. Downstream, the workaround is the one applied above — say it in
unrefined arithmetic, or supply the equation with an `SMTPat` lemma.

## A fifth finding: a discharged side condition is now a live hypothesis

`Kuiper.Math.OnlineSoftmax` was the last regression kuiper produced, and the
only one that is purely about proof performance. Baseline checks the module in
40s; this branch spent half an hour on it and had not finished.

It reduces to six lines with no kuiper in them at all:

```fstar
module RealRepro
open FStar.Real
let abcd_adcb (a b c d : real{b =!= 0.0R /\ d =!= 0.0R})
  : Lemma (a /. b *. c /. d == a /. d *. c /. b) = ()
```

| | goal 5 |
| --- | --- |
| master | 0.20s, rlimit 1.066 |
| this branch | 10.85s, rlimit 2.164 |

The query is *identical* — `--log_queries` gives byte-for-byte the same
`@query` assertion on both. What differs is the assumption stack it is asked
under. `( /. ) : real -> d:real{d =!= 0.0R} -> Tot real`, so each of the four
divisions in the statement raises a `d =!= 0.0R` obligation; those are goals 1-4
and they are trivial on both sides. On master they are discharged inside their
own `push`/`pop` frames and are gone by the time goal 5 is asked, which sees
four hypotheses, all of them `HasType` facts. Here the same obligations survive
into goal 5's frame, which sees eight:

```smt2
(assert (! (not (= @sk_2 (BoxReal 0.0))) :named @hypothesis_10))
(assert (! (implies (and (not (= @sk_2 (BoxReal 0.0))) (not (= @sk_4 (BoxReal 0.0))))
                    (not (= @sk_4 (BoxReal 0.0)))) :named @hypothesis_9))
(assert (! (implies (and (not (= @sk_2 (BoxReal 0.0))) (not (= @sk_4 (BoxReal 0.0))))
                    (not (= @sk_4 (BoxReal 0.0)))) :named @hypothesis_8))
(assert (! (not (= @sk_2 (BoxReal 0.0))) :named @hypothesis_7))
```

Two of those are exact duplicates of the other two, and two of them are
tautologies. None of them carries information the refinement on `sk_2` and
`sk_4` did not already carry. But they are *ground disequalities over reals*,
and nlsat case-splits a disequality into `< \/ >`: four redundant atoms are up
to sixteen extra branches through a nonlinear decision procedure. Nothing about
the goal got harder; the context got noisier in exactly the way this one theory
cannot absorb.

The reason they survive is the shape of the VC. A `requires` is a binder now, so
the obligation attached to an implicit `squash` argument is closed over the
binders in scope and conjoined into the same VC as the body's obligation, rather
than being solved and discharged in a nested frame. That the two copies are
identical says the closure happens twice, once per elaboration path.

This is worth fixing, but the fix is in VC *construction* — deduplicating and
scoping the guards that `Env.push_guard` accumulates for implicit arguments —
not in anything this PR touches, and it needs its own measurement: every
`Lemma` in ulib is affected by how those guards are framed, and most theories
are far less sensitive to redundant hypotheses than nonlinear reals are.

Downstream the workaround is not an rlimit bump but a restatement: writing the
two side conditions as a `requires` rather than as refinements on `b` and `d`
produces one hypothesis instead of four guards, and takes 0.30s against the
refinement form's 11.1s at the same default budget. That is a useful rule of
thumb for anyone hitting this — **if a lemma's arguments are refined and its
conclusion uses each of them under a partial operation, prefer a `requires`** —
and it is also a hint about the eventual fix: the `requires` path already does
the scoping that the implicit-argument path does not.

## The fifth finding, resolved: deduplicating VC conjuncts

Merging `origin/master` turned the fifth finding from a performance note into
two hard failures. Upstream landed a new SMT encoding for `prop`, which adds a
`BoxProp` constructor to `Term` along with

```smt2
(assert (! (forall ((u Fuel) (x Term))
             (! (implies (HasTypeFuel u x Prims.prop) (is-BoxProp x))
                :pattern ((HasTypeFuel u x Prims.prop)))) :named prop_inversion))
```

`is-BoxProp` is a datatype tester, so every prop-typed term in the context is a
potential constructor case-split. Master's VCs absorb that; ours do not, because
of exactly the duplication described above. `FStar.Math.Lemmas.lemma_div_plus`
and `FStar.Math.Fermat` began failing at the default budget. The failing goal
was instructive: the SMT text of the query was *byte-identical* before and after
the merge, and bare `z3` still solved it in 0.9s, but the goal went from **0.087
rlimit to exhausting 5.000** — a purely contextual, ~57x blow-up. Its VC carried
**32 syntactically identical copies** of the guard `n > 0 ==> n <> 0` emitted by
the divisions in the statement, nested under seven layers of
`forall (_: Prims.unit)`.

So the fix is the one this section already predicted, and it is now implemented:
`dedup_vc` in `FStarC.TypeChecker.Rel`. It walks the conjunctive structure of a
VC and replaces a conjunct by `True` when a syntactically identical conjunct has
already been seen in a *goal* position that dominates it. That is sound because
the retained occurrence is proved outright, so the dropped one follows from it.
The set of known conjuncts only ever travels *downwards* — into the right of a
conjunction, the conclusion of an implication, and the body of a quantifier — so
a conjunct found under a binder is never assumed known outside it. Pushing the
outer set *under* a binder is fine: those conjuncts are well scoped in the
enclosing context and therefore mention none of the bound variables, and
`SS.open_term_1` picks globally fresh names, so capture is impossible.
Membership uses `FStarC.Syntax.Hash`'s structural `equal_term`, not a hash
comparison, so a collision costs a missed opportunity and never an unsound drop.

It runs at the single point in `do_discharge_vc` where a goal is handed to
`env.solver.solve` — after tactic preprocessing, after normalisation, and after
`check_trivial`. Nothing upstream of the solver can observe it, so it cannot
perturb unification, inference or tactics.

On `FStar.Math.Lemmas`, against the pre-merge build of this branch:

| | goals in the module | goals for `lemma_div_plus` | wall |
| --- | --- | --- | --- |
| pre-merge, no dedup | 1071 | 41 | 7.8s |
| merged, no dedup | 1071 | 41 | *fails* |
| merged, with dedup | 654 | 10 | 8.4s |

The worst single goal in the module sits at rlimit 4.0 in both the pre-merge
baseline and the deduplicated merge — it merely moves between lemmas, which is
ordinary Z3 luck rather than a change in difficulty.

This is a narrower fix than the section above asks for: it removes the
duplicates at the end rather than avoiding their construction, so
`Env.push_guard` still does redundant work and the compile-time cost of building
those conjuncts remains. Scoping the guards at construction is still worth
doing. But it removes the duplicates from every query, which is what the solver
was actually paying for, and it does so without changing a single downstream
proof.

### The rest of the merge fallout

Three tests moved, and it is worth separating what the dedup did from what the
merge did. `FSTAR_NO_DEDUP_VC=1` turns `dedup_vc` off, which makes the
attribution mechanical.

**`tests/bug-reports/closed/Bug3213b.fst`** is the only one caused by the dedup,
and it is the intended behaviour rather than a regression. The test asserts
`expect_failure [19; 19; 19]`; it now raises two. Its two `forall_elim` calls
differ only in their explicit argument, and `forall_elim`'s precondition
`forall (x:a). p x` does not mention that argument — so the two obligations are
the same formula, and are now reported once. The annotation is now `[19; 19]`.
The cost is real, if small: two failing obligations at two source lines can
collapse to one message. Labelled goals are unaffected, since `equal_term`
compares the range inside `Meta_labeled`, so only unlabelled duplicates merge.

The other two are fallout from #4519, which stopped emitting the *term*
equation `f x == body` for a prop-valued definition, leaving only the formula
equation `Valid (f x) <==> body`. Both fail with the dedup off as well.

**`examples/data_structures/BinomialQueue.fst`** — `find_max_emp_repr_l`'s
vacuous branch. The encoded query is byte-identical to the pre-merge one and the
goal is still provable, but z3 now returns `unknown because (incomplete
quantifiers)` in 0.01s having used 0.049 of its budget: it saturates rather than
running out of resources, and `--z3rlimit 200`, `--fuel 4` and `--ifuel 2` all
leave it exactly where it was. The unsat core from a run without a resource
bound shows why — the new proof needs `prop_inversion`, `prop_validity`,
`true_interp` and `function_token_typing_Prims.l_True`, none of which the old
one used. Naming the intermediate fact (`assert (S.mem k (keys l).ms_elems)`)
restores it. That is the right shape of fix for a saturation failure; an rlimit
bump would not have worked at any size.

**`examples/dsls/dependent_bool_refinement/DependentBoolRefinement.fst`** —
`soundness`'s `T_App` case. This one *is* resource exhaustion, and
`--z3rlimit_factor 2` on the enclosing `#push-options` block is enough; 4 and 8
were also tried and are not needed. It is the one rlimit change in this merge.

### Re-testing EverParse and kuiper against the merged compiler

Both downstream trees were wiped of every `.checked` file and rebuilt from
scratch against the merged compiler. EverParse revised is green again at 417
`.checked` after two changes; kuiper revised is green again at 396 `.checked`
after five. Every failure below was attributed with `FSTAR_NO_DEDUP_VC=1` first:
none of them is caused by `dedup_vc`.

**EverParse, `LowParse.Pulse.Combinators`: an implicit that used to be solved to
the other side's spelling.** `split_nondep_then` and `ghost_split_nondep_then`
pass `nondep_then_eq_dtuple2` where a `(x: bytes) -> Lemma (parse p1 x == parse
p2 x)` is expected. The lemma proves exactly that, and the error printed the
goal and the hypothesis identically — even with `--print_implicits`. The
encoded query showed the real difference:

```
hypothesis: (Prims.dtuple2 U_zero U_zero @sk_1
              (ApplyTT (ApplyTT (ApplyTT const_fun@tok @sk_1) (Tm_type U_zero)) @sk_2))
goal:       (Prims.dtuple2 U_zero U_zero @sk_1
              (Tm_abs_37737479cb6c0218c05fc1830ca134c2 @sk_1 @sk_2))
```

The call site writes the type implicit as `#(_: t1 & t2)`, which elaborates to
`dtuple2 t1 (fun _ -> t2)`, while `nondep_then_eq_dtuple2` states its
postcondition with `dtuple2 t1 (const_fun t2)`. The two are equal only by
delta-unfolding `const_fun` and eta — which the unifier does and the SMT
encoding of a closure cannot. Pre-merge, the implicit was solved to the
`const_fun` spelling and the obligation never reached the solver at all: the
pre-merge query for this definition has two goals, both mentioning `const_fun`
and neither mentioning the closure token. Post-merge the user's spelling
survives, so the obligation is emitted, and z3 saturates on it
(`incomplete quantifiers`, 0.01s, 0.07 of a budget of 5 — no rlimit helps).
Only two upstream commits in the merge touch the typechecker
(`790da6baa1`, which makes `eq_tm` compare binder qualifiers on arrows, and
`bd499fb784`), and I did not pin it to either; what is verified is that the
pre-merge build of this branch checks the module and the merged one does not.
The fix is to write the same spelling on both sides:
`#(dtuple2 t1 (const_fun t2))`.

**EverParse, `CBOR.Pulse.Raw.Format.Serialize.map_peek`:** the subterm ordering
`fst (List.Tot.hd (Map?.v r)) << r`, needed for `depth_cb_pos`'s last binder,
now exhausts the default rlimit (`canceled`, exactly 5.000). The identical
proof still succeeds unaided in `CBOR.Pulse.Raw.Read.map_peek`, so the cost is
the ambient context of this module rather than the goal. `--z3rlimit 10`,
scoped to that one `ghost fn`, is well below the 32 and 64 already used
throughout the file.

The eight kuiper failures are all arithmetic — nonlinear multiplication,
division and modulus — and six of the eight are better fixed by naming the
missing step than by raising a limit:

- **`Kuiper.Divides.lemma_divides_trans`** — `x * f1 == y` and `y * f2 == z` no
  longer give `x * (f1 * f2) == z` on their own; `M.paren_mul_right x f1 f2`
  supplies the reassociation. A second step in the same file
  (`c == (c/a) * a` from `a * (c/a) == c`) needs `M.swap_mul`.
- **`Kuiper.Kahan.kahan_sum`** — the invariant's `new_c %~ 0.0R` was costing
  61 seconds and exhausting rlimit 20. The real-arithmetic core is
  `(s1 -. s0) -. (y -. 0.0R) == 0.0R` given `s1 == s0 +. y`. Hoisted to a
  top-level `kahan_delta_zero` proved in an empty context, the module drops
  from a 61s failure to a 4s success. The ambient context inside the loop is
  saturated with the `_approx_pat` SMT patterns of
  `Kuiper.Approximates.Base`, every one of which fires on the `sub`s in the
  body; that is what made an otherwise trivial goal expensive.
- **`Kuiper.Kernel.GEMM.Copy.Vec2.cp_array2_vec`** — the `while` measure. The
  new index is `(git + 1) * nthr * chunk_et` and stays under `mlen` because
  `chunk_et * nthr` divides `mlen`; chasing that through division, commutation
  and reassociation *inside the loop body* took 303 seconds and exhausted an
  already generous rlimit of 120. A top-level `cp_measure_helper` doing the
  same four `FStar.Math.Lemmas` steps in an empty context is instant.
- **`Kuiper.Sparse.Array.PtsTo.thread_gather_chunks`** and
  **`Kuiper.Kernel.SDPA.Naive.sdpa_probs_spec_slice`** — the two that did get
  an rlimit. Both are resource-bound (`canceled` at exactly the limit, not
  `incomplete quantifiers`), both are `forall`-quantified nonlinear index
  goals with no per-element proof hook to hang a lemma on, and
  `--z3rlimit_factor 2` scoped to the single definition is enough for each. In
  the `PtsTo` case I first tried the structural route — a quantified
  `chunk_cell_offset_forall` — and it discharged the stated goal but simply
  moved the cost onto the accompanying `Seq` bounds obligation, so the scoped
  factor is the honest fix.
- **`Kuiper.Sparse.SPMM.LoadSparse.load_array_vec`** — `n / (nthr * chunk et)
  == n / nthr / chunk et`, a single `division_multiplication_lemma`, was
  exhausting rlimit 30 inside the `thread_live_chunks` unfolding. A top-level
  `load_array_vec_size` proved in an empty context is instant.
- **`Kuiper.Sparse.SPMM.Compute.seq_load_vmprod_cell_lemma`** — the recursive
  case has to recombine `(k1 / chunk et, k1 % chunk et)` back into `k1` to turn
  the `_prop_` form of the invariant into the `_prop` form. The author had
  already written the bridging call to `seq_load_vmprod_row_cell_prop_equiv`
  and left it commented out because SMT had been finding it; uncommenting it is
  the whole fix.
- **`Kuiper.Sparse.SPMM.Barrier.barrier_p_to_q_transform`** — the third and
  last rlimit, and the least satisfying. `barrier_in`'s implicit divisibility
  squashes are spelled `(chunk et * p.blockWidth) /? p.blockItemsK` while the
  `parameters` record refines `blockWidth` with the commuted `(k * chunk et) /?
  blockItemsK`; discharging one from the other misses the default budget by a
  little (`canceled` at 5.000; rlimit 8 suffices). Respelling would touch 69
  binders across the SPMM sources, so this is a scoped `--z3rlimit_factor 2` on
  the single declaration.

Two measurement notes came out of this round. First, `--admit_except` is not a
sound way to size an rlimit: `seq_load_vmprod_cell_lemma` *passes* under
`--admit_except` and fails in the full-module run, because F* reuses one z3
process across a module and the earlier queries change how the later ones
perform. Sizes have to be measured in a full-module run. Second, the
distinction between `canceled` and `incomplete quantifiers` in `--query_stats`
decided every one of these: `canceled` at exactly the limit means a bump will
work, and `incomplete quantifiers` in a fraction of a second means no bump ever
will.

## Testing against pulse-verified-gc, and a three-way A/B/C

EverParse is parsing and low-level imperative code; kuiper is type-level
computation and typeclasses. The third round was run against
[pulse-verified-gc](https://github.com/FStarLang/pulse-verified-gc), a verified
OCaml-style garbage collector: a very large body of *first-order arithmetic*
spec code — heap addresses, word alignment, header bit-fields — with Pulse
implementations on top. It is the most SMT-bound of the three, and it exercises
a part of the system the first two rounds barely touched.

It also forced a change in method. By this point the branch had merged
`origin/master` several times, while pulse-verified-gc pins F* nightly
`ae858eacbd07`. A two-way A/B can no longer distinguish "this PR broke it" from
"upstream broke it in the meantime". So this round is an **A/B/C**: the pinned
baseline, this branch, and a third tree built with plain `origin/master` at
`52f17ab8fd`. Anything that fails in tree C is upstream drift and is not this
PR's to fix.

The result is worth stating plainly. Against the 241 modules of the baseline:

| tree | modules verified | notes |
|---|---|---|
| baseline (nightly `ae858eacbd07`) | 241 | reference |
| plain `origin/master` `52f17ab8fd` | 231 | needs the operator rename *and* an rlimit bump in `GC.Spec.Allocator.fsti` merely to get that far |
| this branch | 241 | with the source changes below |

Plain master needs the same mechanical `op_Subtraction` → `op_Minus` rename this
branch does (upstream's "uniform operator name mangling"), then still fails in
eight places, including every one of the two hardest failures this branch hit —
`GC.Spec.SweepCoalesce.Helpers.combine_extract_nth` and
`GC.Gen.CheneyPreservation.Forwarding` — plus four sites in
`GC.Gen.MinorCollectForwarding` and two in `GC.Spec.Allocator.Lemmas` that this
branch verifies without complaint. The `SweepCoalesce.Helpers` slowdown in
particular (a ~4x regression on a bit-blasting-heavy `logand`/`shift_right`
proof) is attributable to upstream `9c919fce78`, "Encode prop like bool, boxing
to SMT Bool", which introduces the `BoxProp` constructor and shows up as a
literal diff in the generated `.smt2`. None of it is this PR.

### A finding that changes how a regression should be read: gensym instability

Two F*-library modules — `Pulse.Lib.PriorityQueue` and `Pulse.Lib.Array.Core` —
started failing after a `Rel.fst` change that could not possibly affect them.
Dumping `--log_queries` from both compilers and normalising showed the two
`.smt2` files differ **only** in the numbering of gensym'd universe variables
(`uu___79` → `uu___83`, `uu___91` → `uu___95`). Replayed offline through z3, the
old file gives zero `unknown` and the new one gives exactly one, at the same
goal; renaming *part* of the symbol set does not flip it back, so the effect
depends on the whole set.

That is not a semantic regression. It is a proof that was passing with no margin,
knocked over by a shifted fresh-name counter. Any perturbation of the compiler
can do this, so it will happen again, and the diagnostic is worth writing down:

1. Run both compilers with `--log_queries` (the file lands in the *cwd* as
   `queries-<Module>.smt2`).
2. `diff <(sed 's/uu___[0-9]*/UU/g;s/@x[0-9]*/@X/g' A) <(sed ... B)`. If the only
   remaining difference is the `; STATUS:` comment, the inputs are equivalent and
   the compiler change is not the cause.
3. Confirm by replaying each file with `z3 -smt2` and counting `^unknown`. F*
   embeds the per-goal `(set-option :rlimit N)` in the logged file, so an offline
   replay is faithful.

The right response is to fix the *proof*, not to revert the compiler change,
and both were fixed at the source: `almost_to_full_heap`'s induction on sequence
length was deleted outright (`almost_up_implies_heap_down` already gives
`heap_down_at s i` at every index, so a single `Classical.forall_intro` does it),
and `pcm_share` got the `m1`-side permission bound that was already present,
asymmetrically, for `m2`.

### Two compiler fixes

**Uvars in implicit positions are not logical content.** Under this PR a
`Lemma post` is checked by *subtyping between `squash` types*. `Rel` has a rule
that rewrites `squash p <: squash q` into `(_:unit{p}) <: (_:unit{q})`, which is
what makes such a check cheap; it was guarded by "neither side contains a uvar".
An incidental *implicit* uvar — the `#a:eqtype` of `op_Equals` — was enough to
disable it, sending the problem to `Tm_app` congruence instead, whose local
`equal` helper normalises with `[UnfoldUntil delta_constant; ...]`; unfolding
`to_vec`/`from_vec` at width 64 then consumed 32 GB and did not terminate. The
guard is now `has_uvar_needing_congruence`: a uvar that is an implicit argument
of an *interpreted* head can be ignored, while every other uvar is logical
content and must still block the rewrite. (That distinction matters: an earlier
"no flex at all" formulation broke `introduce _ ==> _`, because
`FStar.Classical.Sugar.implies_intro`'s `p` and `q` *are* explicit.)

The restriction to *interpreted* heads was not the first attempt, and the
intermediate version — ignore a uvar in any implicit position — is worth
recording, because it broke EverParse in a way that no `make ci` run would
have caught. `ASN1.Syntax` has

```fstar
let asn1_any_oid (name : string) (supported : list (asn1_oid_t & asn1_gen_items_lk))
                 (pf_wf : squash (asn1_any_prefix_k_wf (Set.singleton oid_id)
                                                       (List.map proj2_of_3 [])))
                 (pf_sup : squash (List.noRepeats (List.map fst supported)))
  = ASN1_ILC sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l []) oid_id ASN1_OID
                                              supported None pf_wf pf_sup)
```

`proj2_of_3` has an implicit `#c : a -> b -> Type`. In the type of `pf_wf` the
list is empty, so `#c` occurs nowhere else and nothing local determines it. The
one thing that does determine it is checking the body: `pf_wf` is passed to
`ASN1_ANY_DEFINED_BY`, whose expected type for that argument mentions the *same*
`List.map proj2_of_3 []` with `#c` already solved, and congruence on that
`squash <: squash` problem commits it. Rewriting the problem into refinement
subtyping instead hands it to the SMT solver as an implication, which solves
nothing; `#c` then survived typechecking and was *generalized*, giving
`asn1_any_oid` a spurious leading `#_: Type` binder. Every call site in
`ASN1.X509` then failed with `Error 66: Failed to resolve implicit argument`.

Two things about this are worth remembering. First, the symptom appeared three
commits away from its cause, in a file whose `.checked` had been reused across
compilers — a stale `ASN1.Syntax.fst.checked` also masked the *fix* on the first
attempt, which sent the diagnosis down a blind alley. When a regression is about
inference rather than proof, the caches of the *dependencies* have to be wiped
too. Second, the useful oracle was not the error but the inferred type: running

```
let _ = assert True by (print (term_to_string (tc (cur_env ()) (`ASN1.Syntax.asn1_any_oid))))
```

under the branch and under `origin/master` showed `#_: Type ->` present in one
and absent in the other, and reduced a 3000-line EverParse module to a
fifteen-line test case.

Regression tests: `tests/bug-reports/closed/SquashSubtypingDivergence.fst`, which
now covers both directions — the `GC.Lib.Header` shape that must fire, and the
`asn1_any_oid` shape that must not.

The unbounded normalisation inside that `equal` helper is the more fundamental
problem and is left as a follow-up: `Env.step` has no fuel constructor, so
bounding it is not a one-line change.

**Eta-expansion across a missing `requires` binder.** `ToSyntax` omits the
`#(_:squash pre)` binder when `pre` is syntactically `True`, so
`Lemma (ensures q)` has one binder *fewer* than `Lemma (requires p) (ensures q)`.
`Classical.move_requires`' argument binder is `$_:`, i.e. `Equality`, which
forces `use_eq` and rules out ordinary subtyping, so the gap has to be bridged
in `try_eta_expand_to_expected_typ`. It now rebinds a trailing expected binder
whose sort is `squash ?p` with `?p` *uvar-headed* at `squash True`, letting
`?p := True` fall out of the ordinary check. A *concrete* expected precondition
is left alone, so genuinely strengthening a precondition is still rejected.
Regression test: `tests/bug-reports/closed/MoveRequiresNoPrecondition.fst`.

### The source changes in pulse-verified-gc

Every one of them is either an improvement or a documented stabilisation; none
is a large rlimit bump. The pattern that dominates is the one kuiper already
suggested, and pulse-verified-gc makes overwhelming:

> When a trivial arithmetic fact times out inside a large proof, hoist it to a
> top-level lemma proved in an empty context. It is the *context* that is
> expensive, not the goal.

- `GC.Gen.CheneyPreservation.Forwarding` needed two: `(a + k*8) % 8 == 0` from
  `a % 8 == 0`, and `b + ((a-b)/8)*8 == a` from `a % 8 == b % 8 == 0`. Both are
  one-line consequences of `FStar.Math.Lemmas`. Inline they were `canceled` at
  rlimit 120; hoisted, the whole module verifies with a **maximum used rlimit of
  7.1**.
- `GC.Gen.Promote.promote_preserves_field_at` and
  `GC.Gen.MinorHeap.minor_reset_tag_zero`: same treatment, both back to the
  module's base rlimit. The `MinorHeap` one is also a small lesson in `assert_norm`:
  the fact was `U64.v (U64.logand 0UL 0xFFUL) == 0`, and normalising it drives the
  evaluator through `UInt.to_vec`/`from_vec` at width 64. Deriving it from
  `UInt.logand_le` instead is both cheaper and context-independent. It has to be
  *parameterised* over the header, though — as a closed fact Z3 will not do the
  congruence step from `hdr == 0UL` under `--ifuel 0`.
- `GC.Gen.Cheney.SimOne`: two `UInt64` facts hoisted; the module went from
  failing after ~130 s to verifying in **8 s**.
- `GC.Gen.TwoPassEquiv.two_pass_pointwise`: **an ascription bug this PR makes
  visible.** The proof writes
  `let obj : obj_addr = IndDesc.indefinite_description_ghost obj_addr (fun obj -> ...)`.
  Under this PR `indefinite_description_ghost` returns a *refined* result
  `x:a{p x}`; ascribing the unrefined `obj_addr` throws the refinement away and
  leaves Z3 to re-derive `p obj` from the definitional equation. Deleting the two
  ascriptions fixes it. This is the general shape to look for when a `Pure`/`Ghost`
  result stops carrying its postcondition: an ascription that used to be free now
  weakens the type. `GC.Impl.Allocator.init_heap_normal_lemma` is the same story
  read in the other direction — there an ascription had to be *added*, to strip
  `write_word`'s new result refinement where the unrefined `heap` was wanted.
- `GC.Spec.Sweep.sweep_object_preserves_other_header`: the shared conclusion is
  now asserted at the end of *each* of the four branches rather than once after
  the `if`. A minimal test confirmed that lemma postconditions are **not**
  generally lost across a join, on this branch or the baseline, so this is proof
  robustness rather than a compiler workaround: the branches reach the conclusion
  through different intermediates and the join keeps only what is stated.
- Two scoped rlimit bumps, each with its `--query_stats` measurement recorded in
  a comment next to it: `GC.Gen.CheneyBFS.forward_one_queue_prefix` 10 → 20 and
  `GC.Spec.Allocator.Lemmas.Part1.alloc_split_facts_part1` (`canceled` at exactly
  5.000; 6.925 used at 10). Nothing larger was needed.
- Three more well-typedness side conditions moved out of the context that was
  drowning them. `GC.Gen.PromoteUpdate.Field` is the sharpest: the `ensures` of
  `update_all_objects_aux_field_effect` applied `U64.uint_to_t` to
  `U64.v obj + j * 8`, so `FStar.UInt.size _ 64` and the `hp_addr` refinement
  were being discharged in that lemma's full context — 21 s and 34.6 rlimit units
  against a budget of 12. Adding the bound as an extra `requires` conjunct did
  *not* help; the context, not the goal, was the problem. The fix is a **total
  function with a junk value**: a private
  `field_addr : U64.t -> nat -> GTot hp_addr` returning `zero_addr` when the
  address is out of range, so the obligation is discharged once, at the
  definition, in an empty context, plus a `field_addr_v` lemma naming the
  equation under the real precondition. The lemma now uses **3.3** rlimit units.
  (A first attempt returned `U64.t`; the caller then demanded `hp_addr` and the
  problem simply moved. The return type has to be the refined one.)
  `GC.Impl.MarkBounded.wosize_offset_fits` and
  `GC.Gen.MinorHeap.infix_parent_below` are the same idiom applied to
  `U64.mul wz mword` inside a Pulse `fn` and to `addr >= infix_parent minor addr`
  in all four infix branches of `CheneyPreservation.Frame`.
- **The one case where naming a *case analysis* was the fix, not naming a fact.**
  `GC.Spec.SweepCoalesce.Helpers.combine_extract_nth` is a bit-level proof — an
  8-way `select_byte`, a `shift_right` by the nonlinear `8 * k`, sixteen
  `UInt.nth` lemmas — and it was `canceled` at rlimit 200, at 400, and at 800.
  For each byte `m` above the extracted byte `k`, the `m`-th shifted byte
  contributes nothing at bit `j`; that follows from `j >= 56 - 8*k` and `m > k`,
  but only after a case analysis with **both** `8*k` and `8*m` symbolic. Writing
  the seven instances out, with `m` a literal so `8*m` is a constant, takes the
  lemma from timing out at 800 to using **42 of its declared 200**. Worth
  stressing: this lemma also fails on plain `origin/master`, so it is not a cost
  of this branch — it is where the ~4× slowdown from upstream `9c919fce78`
  "Encode prop like bool, boxing to SMT Bool" surfaces. The fix is upstreamable
  as-is.
- Two quantifier weakenings hoisted for the same reason as the arithmetic:
  `Forwarding.fwd_classified_weakens` (`fwd_valid_or_infix` is `fwd_classified`
  with the existential witness dropped, but the weakening is *under* a
  quantifier) and `Allocator.Lemmas.Part2.hd_address_v`. The first is the best
  illustration in the whole campaign of why isolated probes are not evidence:
  the goal took **0.1 s and 0.34 rlimit units** when the module was checked on
  its own, and timed out at rlimit 20 in a full build. Whether the solver finds
  the instantiation depends on the rest of the module, so "it passes in
  isolation" means nothing. Every fix here was confirmed by a clean rebuild.
- `GC.Gen.MinorHeap.minor_zero_header_fields`: decoding a zero minor header into
  wosize 0 / tag 0 needs the bit-vector encoding of `shift_right` and `logand`.
  All three SPOT nurseries were doing that inside a proof whose context already
  fixes several *other* header words, and all three timed out. Proving it once
  for an arbitrary `minor_state` fixes all three call sites.

### Method notes

`--query_stats`' reason-unknown is the classifier, and it was right every time:
`canceled` at exactly the limit means a bump *may* work; `incomplete quantifiers`
in a fraction of a second means a fact is missing and no bump ever will.
`--admit_except` remains unsuitable for *sizing* an rlimit — F* reuses one z3
process per module, so earlier queries change how later ones perform — but it is
fine for extracting a single query with `--log_queries`. And `--admit_except`
takes exactly one name: a comma-separated list silently admits the whole module
and reports success.

## Two benchmark outliers, and what they were

The benchmarking bot on this PR reports the change as roughly neutral overall
(geometric mean 1.003x memory, 0.989x time, 308s less wall clock in total), with
some large wins — `ExtUIntMask` -55.8%, `BVExtend` -94.4%,
`Lib.Sequence.Lemmas` -49% — and two large outliers. Both turned out to be worth
chasing: neither is really about this branch's design, and one of them is a
long-standing performance bug in `Rel`.

### `Bug3800.fst`: `forall x. phi ==> True`

`tests/bug-reports/closed/Bug3800.fst` went from 0.47s/94MB to 6.18s/330MB. A
size-parameterised family of the same shape shows why: the cost is *exponential*
in the nesting depth of the test's sixteen chained `let v = if ... then ... else v in`,
while on master it is linear. The SMT query is not the problem — it is in fact
*smaller* on this branch. `--profile` puts 5.9 of the 6.2 seconds inside
`Rel.sub_comp` -> `Rel.simplify_vc` -> `Normalize.normalize`.

The guard being normalized is

```
forall (_: u32). _ == <the entire sixteen-deep let/match body> ==> True
```

It comes from the refinement/refinement case of `solve_t'`. The left-hand side
of the subtyping problem is the definition's computed type, which on this branch
carries the definitional equation as a *refinement* (on master the same fact
lives in a `Pure` wp and is already CPS-flattened, so it normalizes linearly).
The right-hand side is the annotated `Tot u32`, which is unrefined —
`force_refinement` turns it into `x:u32{True}` purely so that the two sides have
the same shape. The case then builds `forall x. phi1 ==> True`.

That guard is trivial, but nothing noticed: `mk_conj`/`mk_imp` do not simplify,
so `simplify_vc` dutifully normalized the antecedent first, and normalizing a
chain of sixteen `let`s over a `match` duplicates the continuation into both
branches.

The fix is two lines of `mk_imp_simp`/`mk_conj_simp` (which already existed in
`Syntax.Util` and short-circuit on `is_t_true`) plus an `is_t_true` test before
`guard_on_element`, which also avoids a needless `universe_of` call on the
binder's sort. `EQ` is deliberately left alone: `phi1 <==> True` is `phi1`, not
`True`.

This is not a regression this branch introduced so much as one it exposed —
master reaches the same code, just with an antecedent that happens to be cheap to
normalize — and the fix is independent of everything else here. After it,
`Bug3800.fst` runs in **0.31s/84MB**, i.e. faster than master's 0.47s/94MB.

### `Quicksort.Base.fst`: a proof that was passing by luck

`pulse/share/pulse/examples/Quicksort.Base.fst` went from 22s to 87s. Profiling
puts all of the delta in Z3 (9.8s -> 45.8s of aggregate query time), and
`--query_stats` narrows it to two lemmas, `transfer_larger_slice` and
`transfer_smaller_slice`, under a `#push-options "--retry 10"`.

Both compilers fail the *same* goal — the third `assert`, which re-indexes a
lower bound on `s` into a lower bound on `Seq.slice s (l - shift) (r - shift)`.
Master happens to succeed on its second retry; this branch exhausts all ten
(~2.8s each) and then succeeds only once F* escalates `ifuel` to 2. Extracting
the goal with `--log_queries` and running it standalone confirms it: with a fresh
solver the goal is `unknown` at `ifuel 1` on *both* compilers, under every
hypothesis configuration I tried. The three-`assert` proof was never actually
working; it was winning a race against `--retry`.

The missing step is that the goal mentions
`Seq.index (Seq.slice s (l - shift) (r - shift)) k`, which the `SMTPat` on
`Seq.lemma_index_slice` rewrites to `Seq.index s (k + (l - shift))`, whereas the
hypothesis has to be instantiated at `k + l`, giving
`Seq.index s ((k + l) - shift)`. The two index terms are equal only by linear
arithmetic, so whether E-matching bridges them depends on whether the arithmetic
solver has already merged their congruence classes.

Replacing the three `assert`s with an `introduce forall ... with introduce _ ==> _`
that names the witness `j = k + l` explicitly — which puts `Seq.index s (j - shift)`
in scope and makes the instantiation immediate — makes the goal go through
deterministically, and the `--retry 10` and `#restart-solver` are no longer
needed. The file now takes **7.6s on this branch and 7.7s on master**, against
14.4s for master before the change.

## Merging master's `NDET` effect

While this branch was in review, master landed `NDET`: a primitive effect that is
*nondeterministic but terminating*, so the lattice becomes
`PURE ~> NDET ~> DIV` with an explicit `NDET ~> TAC` lift. That is the same
territory this branch rewrites, so the merge is worth describing.

Most of the nine conflicts were mechanical. Master extended hardwired lists like
`src = PURE || src = NDET` at exactly the sites where this branch had introduced
the class predicates of "An effect abbreviation is a bare alias". `NDET` is both
a lift source and a lift target, so it cannot be folded into either neighbouring
class; it gets its own `PC.is_ndet_effect_lid` — covering `NDET`, `Ndet` and `Nd`
— with `PC.primitive_ndet_lid` and `U.is_ndet_effect` routed through it, exactly
as the other three classes are, and each site becomes a disjunction of two class
predicates. Two of master's hunks call `Env.norm_eff_name`, which this branch
deleted: `ToSyntax` resolves abbreviations now, so `lbeff` and `comp_effect_name`
already name a root effect and there is nothing to normalize.

`FStar.Pervasives.fsti` needed a fix that was *not* in a conflict hunk, and so
merged silently into something the compiler rejects. Master writes
`sub_effect PURE ~> NDET` and `NDET ~> DIV`, but on this branch `PURE` and `DIV`
are abbreviations and a lift must name the effect itself. These become
`Tot ~> NDET` and `NDET ~> Div`, and the direct `Tot ~> Div` edge is dropped:
`Env.update_effect_lattice` closes the lattice transitively as each edge is
added, so composing the two gives it back.

The one real decision is at the top level. Master replaced `check_top_level`'s
`bool` result with a three-way action so that a *terminating* effect is masked
silently — no warning 272, no `nonempty` obligation — while this branch had
independently changed the same function from `lcomp` to `comp`. Both apply. But
this branch also **drops the refinement it infers for the result type** when an
effect is masked, on the grounds that a postcondition under partial correctness
only holds if the computation returned. `Mask_effect_silently` is precisely the
case where it does return, so the refinement is *kept* there and dropped only for
`Mask_effect_and_warn`.

That is safe because it cannot leak a defining equation `_ == e`, which is what
would let the solver identify two separate calls of a nondeterministic
computation. Such an equation is only ever introduced by
`maybe_assume_result_eq_pure_term`, and `should_return` gates it on the
computation being pure or ghost — which `NDET` is not. Checked rather than
argued: with `assume val f : unit -> Nd (x:int{x > 0})` and `let g1 = f ()`,
`assert (g1 > 0)` proves, while `assert (g1 == g2)` and `assert (g1 == f ())`
both fail as they must. Master's own `TestNd.fst` passes unchanged, including
its universe test — `NDET` is `total` with no representation, so the rule of
"A total effect's universe comes from its representation" answers `u_res` and
`unit -> Nd (Type u#0)` is still `Type u#1`.

One inconsistency is left deliberately. Master makes `NDET` the primitive
spelling with `Ndet`/`Nd` as abbreviations, which is the opposite of the
convention here, where the short name is primitive (`Tot`/`GTot`/`Div`) and the
all-caps name is the abbreviation (`PURE`/`GHOST`/`DIV`). Renaming a feature that
has just landed is churn that belongs in its own change, not in a merge.

## User-visible changes

- `assume_safe`'s argument is now `squash False -> Tac a`, not `unit -> Tac a`.
  Write `assume_safe (fun _ -> ...)`, not `assume_safe (fun () -> ...)`.
- `apply` now works on lemmas; `pose_lemma` is joined by `pose_apply`.
- A failed `()`-against-`squash` check reports **"Assertion failed"** rather than
  "Subtyping check failed" — the obligation really is an assertion now.
- The resugarer folds `#(squash P) -> Tot (x:t{Q x})` back into
  `Lemma (requires P) (ensures Q)`, so error messages and IDE hovers read as
  before. Squash binders print as hypotheses rather than as arguments.
- **Effect abbreviations are bare aliases.** `effect M = N` is canonical; the
  eta-expanded `effect M (a:Type) = N a` is still accepted. Anything else — extra
  binders, a right-hand side that is not an eta-expansion of an effect name, or a
  `requires`/`ensures` on the right-hand side — is now rejected with Error 316
  instead of being silently dropped. See "An effect abbreviation is a bare alias".
- The `effect M = N <: ...` (`redefine_effect`) form is gone from the grammar.
- The `[attributes ...]` clause on an effect declaration is gone. It has been
  impossible to write since Dijkstra Monads for Free removed the `CPS` flag.
- `sub_effect` must name effects, not abbreviations: write `sub_effect Tot ~> M`,
  not `sub_effect PURE ~> M`. The error message names the effect to write.
- A universe application on an effect (`Tot u#0 int`) is rejected rather than
  accepted and discarded.
- `--ext optimize_let_vc` is inert. The behaviour it selected is now the only
  behaviour; existing flags in downstream Makefiles need no change.
- `introduce` and `eliminate` no longer bind a name for the hypothesis: write
  `with e`, not `with h. e`. The hypothesis is an implicit `squash` binder that
  F* puts in the proof context of `e` itself, so there is nothing to name.
  `with h. e` is rejected with a message saying so.
- `Classical.move_requires*` applied to a lemma that has *no* `requires` clause
  is now a no-op rather than an error. Such a lemma has no `squash` binder to
  move, so it has one binder fewer than `move_requires` expects; the gap is
  bridged by `try_eta_expand_to_expected_typ`, which binds the missing
  precondition binder at `squash True` when the expected precondition is still
  an unresolved uvar (a *concrete* expected precondition is left alone, so a
  genuine strengthening is still checked). This keeps a very common idiom
  working. Note, though, that the wrapper is not *wanted*: `Lemma (ensures Q)`
  is now literally `Tot (squash Q)`, which is what `Classical.forall_intro*`
  expects, so the lemma can be passed directly. Several vacuous `move_requires`
  wrappers in ulib were deleted.
- **Accepted regression:** for a call through a let-bound alias, a precondition
  failure is localized to the alias rather than to the call.
- **Accepted regression:** a `Pure`/`Ghost` with an `ensures` now returns a
  *refined* type, so an implicit solved from such a result picks up the
  refinement — most visibly for polymorphic equality, where `SZ.v n == cap`
  needs `(SZ.v n <: nat) == cap`. `Prims.eq2` already carries the
  `[@@@unrefine]` binder attribute that fixes this; promoting it from
  `--ext __unrefine` to the default is proposed as a follow-up. Likewise, a
  lemma's statement is now part of its *type* and so participates in
  unification, which can pin an implicit that used to be left to the expected
  result type. See `regression_questions.md` for both, worked out in detail.
  The same thing bites a container: `Ghost.hide (cbor_map_sub m s)` infers
  `Ghost.hide`'s implicit at `cbor_map_sub`'s *refined* result, giving a
  `Ghost.erased (m:cbor_map{...})` where a `Ghost.erased cbor_map` was meant, and
  the mismatch surfaces later as an unprovable `l_True == <the ensures>`. Give
  the implicit explicitly: `Ghost.hide #cbor_map (...)`.
- **Accepted regression:** a precondition is a *trailing implicit binder*, so an
  arrow that has one has one binder more than an otherwise identical arrow that
  does not. Subtyping now eta-expands to bridge that gap (see "Testing against
  EverParse"), so a point-free definition whose implementation is *more general*
  than its interface still typechecks. The eta-expansion is only attempted for
  pure and ghost computations and only when the surplus binders are implicit, so
  a few point-free idioms still need to be written out: passing `( + )` where a
  two-argument arrow is expected may need `(fun a b -> a + b)`.
- **Accepted regression:** an implicit can be pinned by a *later* argument before
  the constraint from an earlier one is processed. If argument `n` gives `?u` the
  rigid lower bound `t{phi}` while argument 1 only wants `t <: ?u`,
  `solve_flex_rigid_meet` fires with a single bound in hand, sets `?u := t{phi}`,
  and turns the earlier constraint into an SMT obligation that cannot be proved.
  This PR makes it more reachable because a lemma's statement is now part of its
  type. Instantiate the implicit explicitly at the call site.
- **Accepted regression:** a `match`/`if` scrutinee's refinement is not always
  available in the branches, so `if strong_excluded_middle p then ...` may no
  longer see `b = true <==> p`. Bind the scrutinee with an explicit refined
  annotation.
- **Accepted regression:** in a chain of *nested* calls whose results are refined
  (``x `logand` lognot ((lognot 0uL `shift_right` a) `shift_left` b)``),
  only the outermost result's refinement is now attached; the intermediate ones
  are lost. Let-bind each intermediate operand — the idiom EverParse already used
  for its `UInt8` instances of the same code — and the refinements come back.
- **Accepted regression:** an `assert` elaborates `==` at the *refined* type of
  its operands, which can add a side condition that did not exist before
  (`assert (a *. (b /. a) == b)` for `a b : perm` now carries `>. 0.0R`).
- **Accepted regression:** a module-local alias of an imported definition is not
  necessarily SMT-unfoldable to it when the module's interface has a `val` for
  the alias. `assert_norm` of the equation restores it.
- **Accepted regression:** Pulse's typeclass-driven
  `intro (Trade.trade A B) #emp fn _ {...}` no longer resolves its `introducable`
  constraint; call `Trade.intro_trade A B emp fn _ {...}` directly.
- **Accepted regression:** `coerce_eq () x` infers its source type from `x`, so
  when `x` is the result of a function with an `ensures` it is the *refined*
  type, and the `()` is then asked to prove that a refinement equals its own
  underlying type. Ascribe the argument at the type intended
  (`coerce_eq () (parse_nlist n p <: parser _ (nlist n t))`) --- the same
  ascription EverParse already wrote for the neighbouring serializer.
- **Accepted regression:** a proof that was already near the solver's limit can
  tip over it, because every lemma called in a Pulse block leaves its
  postcondition — now a *refinement*, and so a hypothesis — in scope, and the
  goal is buried among them. Two EverParse proofs needed the same remedy: state
  the obligation as a small standalone lemma, whose context contains only what
  the proof needs (`LowParse.PulseParse.Sum.dsum_tag_is_strong_prefix`,
  `CDDL.Pulse.Parse.ArrayGroup.half_plus_half_eq`). Both then verify *faster*
  than before, and two `--z3rlimit` bumps that had looked necessary turned out
  not to be.
- **Accepted regression:** a lemma stated point-free over a function that has a
  `requires` (`ensures (inj (f x))`, where `f x` is a partial application
  awaiting the squash binder) is eta-expanded at each use, and two eta-expansions
  of the same term are two distinct closures to the solver, so the lemma's
  conclusion no longer matches the goal. Removing the `requires` in favour of a
  refinement on the argument's own type removes the eta-expansion and the
  problem: this is what `ASN1.Spec.Sequence` and `ASN1.Spec.Any` do.
- **Accepted regression:** the proposition a `squash`-typed *argument* proves is
  no longer published as a fact to the enclosing goal, so a `coerce_eq (_ by tac) x`
  whose two types are only equal after normalisation leaves the solver unable to
  relate them. State the equation once, with the same tactic, before the use:
  `assert (a == b) by tac`. See the section above for the full diagnosis; this is
  `CDDL.Pulse.Parse.MapGroup.impl_zero_copy_map_zero_or_more_aux`.
- **Accepted regression:** when a definition's precondition is a predicate over
  a scrutinee that the body then `match`es, the branch may no longer see what
  the precondition says about the *branch's* pattern variables. The `squash`
  hypothesis is in scope, but as an opaque `HasType` fact it does not drive the
  solver to unfold the predicate at the refined scrutinee. Restate the
  consequence with a `Lemma` taking the precondition and concluding what the
  branch needs, called with `[@@inline_let] let _ = ... in` at the head of the
  branch — the idiom EverParse already uses elsewhere. This is
  `CDDL.Pulse.AST.Bundle.impl_bundle_wf_map_group_zero_or_more`, which needed
  `typ_bounded ... key` and `... value` in its `WfMZeroOrMore` branch.
- A top-level `let x = assert p` now has type `squash p`, so `p` becomes a fact
  for the rest of the module. Ascribe `: unit` where that is not wanted --
  in particular `let _ : unit = assert False`, which otherwise poisons
  everything after it.
- `assert`s that used to be discharged inside a `squash (...)` argument no
  longer contribute to the enclosing definition's own refinement; hoist the
  lemma call out of the `squash`.
- `apply (`magic)` fills in `magic`'s anonymous `unit` argument itself; a
  following `exact (`())` now fails with "no more goals".
- `fail` returns a refined `unit`, so an unannotated tactic whose body ends in a
  `match ... | [] -> fail ...` infers a refined result type. Annotate `: Tac unit`.

## Costs

- **Extraction ABI.** A `#(squash P)` binder carries no computational content,
  so extraction drops it — both the binder and the matching argument — and the
  ABI of a function with a `requires` clause is unchanged. The two sides have to
  stay in agreement, which is where the extraction bug found by the EverParse
  run came from; see above.
- **Solver time.** 15 rlimit adjustments across ulib, Pulse, `examples` and
  `doc`. In aggregate there is no regression: a from-scratch verification of
  ulib's 319 modules takes 1m35s wall at `-j16`, or 13.2 CPU-minutes, against
  the 14m58 recorded for the previous design. The baseline's measurement
  conditions are not documented, so read this as "no regression" rather than as
  a precise speedup.
- **Reflection.** `comp_view` keeps its constructors; `C_Lemma`/`C_Eff` report
  `pre = True`, since a precondition is now a binder on the arrow and out of the
  view's reach. The postcondition *is* recovered from the result-type
  refinement, and `inspect_comp`/`pack_comp` round-trip. Giving the view an
  honest precondition means changing the view type, which needs its own stage0
  bump and is deliberately left to a follow-up.

## A documented limitation

`tests/micro-benchmarks/Positivity.fst`'s `neg_match` now also raises a spurious
Error 19 on a definition that is rejected anyway. When a *closed* scrutinee makes
`subst_pat_bvs_in_res_typ` fire and a branch builds an arrow, the branch must
transport its result type across `t == Some?.v g` — and F*'s SMT encoding gives
arrow types no congruence, since each arrow is encoded as its own constant. This
is unprovable on the pre-refactor compiler too. Every parameterized form of the
same type-level match verifies.

## Validation

`make ci -j48 -k` from a fully wiped tree — `stage{1,2}/{ulib,fstarc}.checked`,
`pulse/build/lib.pulse.checked`, and every `_output` and `_cache` directory under
`tests`, `pulse`, `doc` and `examples` — exits **0**. That covers `make 1`,
`make 2`, `make 3` and `make test` (which is `tests`, `examples` and `doc`, at
stage 3, with Pulse), plus `boot-diff`, `test-2-bare`, `stage2-unit-tests` and
`fsharp-all`. Note that test `.checked` files live in `_cache` as well as
`_output`; wiping only the latter is what let several failures hide.

`ci` already runs stage 3, `examples` and `doc` via `_test`, so it needed no
change.

Both benchmark outliers reported by the PR's benchmarking bot are fixed and the
fixes are in that run: `Bug3800.fst` is 0.31s / 84MB against `master`'s 0.47s /
94MB, and `Quicksort.Base.fst` is 7.6s against `master`'s 7.7s (`master` was
14.4s before the same change was applied to it). See "Two benchmark outliers".

Beyond `ci`, EverParse's `fstar2` branch verifies and extracts end to end
against this compiler, from a clean tree, after the downstream edits catalogued
above. The A/B baseline build with EverParse's pinned toolchain reported zero
errors, so that catalogue is the complete list of differences this PR makes to a
large external codebase: **32 files, +246/-102 lines**, made up of explicit
implicit arguments and type ascriptions, `assert`s restating a fact the solver
used to be handed, four small helper `Lemma`s, one `Ghost.hide`, two implicit
type annotations respelled to match the lemma they are passed to, and three
rlimit bumps. Each of the five load-bearing workarounds was re-tested against the final
compiler with the pristine source restored, and each is still required; none is
masking a bug that has since been fixed.

Kuiper is the second such run, and the same statement holds for it: 396 modules,
green from a clean tree, against a baseline of 396 green modules built with the
F* fork kuiper pins; **27 files, +354/-48 lines** of downstream difference,
catalogued above, of which a good part is the comment on each change explaining
why it is there. Both downstream trees were re-verified from scratch against the
final compiler, after the last typechecker fix and after the earlier merge with
`origin/master`, not against the compiler each regression was found on. The
final numbers are EverParse 417 `.checked` and kuiper 396 `.checked`, both at
exit 0, matching their baselines exactly.

pulse-verified-gc is the third, and the largest of the three: **241 `.checked`
plus the `spot` sub-build, both at exit 0 from a clean tree**, against a
baseline of the same 241 built with the F* nightly it pins. The downstream
difference is **8 commits**, all of them named lemmas and case analyses rather
than budget increases -- the two scoped rlimit bumps listed above are the only
ones, and one *reduction* came out of it (`combine_extract_nth` went from
timing out at rlimit 800 to using 42 of its declared 200).

A caution that this run produced and the earlier two did not: **an isolated
module check is not evidence.** `Forwarding.cheney_promote_fwd_valid_or_infix`
took 0.1 s and 0.34 rlimit units when its module was checked on its own, and
timed out at rlimit 20 in a full build of the same tree, with the same
dependency `.checked` files. Fixing one blocker also exposes the next: a `-k`
build stops at ~176 `.checked` when an early spec module fails, so error counts
between runs are not comparable. Every fix reported here was confirmed by a
clean rebuild, not by a probe.

All three downstream trees were rebuilt one final time, from clean, against the
compiler that includes the two benchmark fixes: EverParse **417 `.checked`,
exit 0**; kuiper **396 `.checked`, exit 0**; pulse-verified-gc **exit 0 on both
the main build and `spot`**. Those are the same counts as their respective
baselines.

Those three numbers were taken at `5209ef174b`, immediately before master's
`NDET` effect was merged in. After that merge, `make ci -j48 -k` is again exit 0
from a fully wiped tree, and **EverParse was re-verified end to end against the
merged compiler — verification and extraction to C, Rust and OCaml, exit 0 with
no F\* errors, at the same 417 `.checked` as its baseline**. Since
`FStar.Pervasives` changed, every downstream `.checked` file was invalidated by
dependency hash, so that run re-checked the tree rather than replaying a cache.
Kuiper and pulse-verified-gc were not re-run against the merged compiler; their
numbers stand as of `5209ef174b`.
