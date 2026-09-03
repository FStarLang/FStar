# Make `Tot`/`GTot`/`Div` primitive, and move specifications out of computation types

This replaces the design in #4508 / #4510 (pushing an *expected postcondition*
through the typechecker). That approach kept the Hoare specification inside a
`comp_typ` and worked around the consequences; this one removes it from
`comp_typ` altogether, so the consequences do not arise.

56 commits, 268 files, `+4196 / −2021`.

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
  effect_name : lident;
  result_typ  : typ;
  flags       : list cflag;
}
and comp' = | Comp of comp_typ
```

A computation type is now a label and a result type. Obligations live in
`guard_t`, where they were always meant to live.

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

The `cflag` list shrank too. `MLEFFECT` is gone: every site that set it did so
exactly when `effect_name` was already `FStar.All.ML`, and every site that read
it already tested the name first. `TOTAL` survives, but with one narrow job
instead of four. It used to be sprinkled on every `Tot`-named comp, residual
comp and `bind` result, where it merely restated the effect name; now it is set
in exactly one place, `ToSyntax.desugar_comp`, and records the one fact the name
does *not* carry — that this comp's effect is an *abbreviation* whose root is
`Tot`, such as `Lemma`. Abbreviations are not unfolded until the typechecker,
and `Syntax.Util.is_total_comp` has no env, so the flag is the env-free record
of that fact. Dropping it entirely breaks `Bug1953.fst` (`type t = | A : int ->
X t` for `effect X a = Tot a` is rejected as "constructors cannot have effects")
and leaves partially-applied lemmas unrecognised as pure, so their trailing
implicit is never instantiated. With `TOTAL` no longer redundant,
`TypeChecker.Util.weaken_flags` became dead and `mk_bind` lost its `flags`
parameter, along with the standing `TODO` about `bind`'s flags being
inconsistent with the comp it returns.

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
  ==>  bs -> #(_ : squash P) -> Tot (squash Q)     flags = [LEMMA; SMTPAT pats]
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

It does not shift. The `LEMMA`/`SMTPAT` flags are kept on the innermost `Tot`
and the post is written with the `squash` fvar, so the encoder recovers
everything structurally: `pre` from the trailing squash-typed implicit binder,
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
`cache_version_number` 93 → 94 is mandatory (and 94 → 95 later, for dropping
`MLEFFECT` from `cflag`) — and it bought the first honest
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
skipped). It found four more typechecker bugs, all fixed here:

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
  there, because not every producer of a term runs it through the elaborator
  first. Core then failed with `Unexpected term: Tm_unknown`. It now falls back to
  the definition's inferred type when the annotation is absent, which is sound:
  an unannotated `let`'s type *is* its definition's type, and the subtyping check
  it would otherwise perform is then reflexive. Only reachable through Core, so
  in practice only through Pulse.
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
(A sixth problem, in the SMT encoding rather than the typechecker, was
root-caused but deliberately **not** fixed; see below.)

One bug was root-caused but deliberately **not** fixed; see below.

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
code. One EverParse definition (`LowParse.PulseParse.Sum.accessor_dsum_tag`) hits
it; the fix there is the general workaround, which is to state the precondition
as a refinement on an argument's own type instead:

```fstar
val g (l: list a { pre l }) : ...        // instead of  (l: list a) : Pure _ (requires pre l) _
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

## User-visible changes

- `assume_safe`'s argument is now `squash False -> Tac a`, not `unit -> Tac a`.
  Write `assume_safe (fun _ -> ...)`, not `assume_safe (fun () -> ...)`.
- `apply` now works on lemmas; `pose_lemma` is joined by `pose_apply`.
- A failed `()`-against-`squash` check reports **"Assertion failed"** rather than
  "Subtyping check failed" — the obligation really is an assertion now.
- The resugarer folds `#(squash P) -> Tot (x:t{Q x})` back into
  `Lemma (requires P) (ensures Q)`, so error messages and IDE hovers read as
  before. Squash binders print as hypotheses rather than as arguments.
- Effect abbreviations may now carry an `ensures`.
- `introduce` and `eliminate` no longer bind a name for the hypothesis: write
  `with e`, not `with h. e`. The hypothesis is an implicit `squash` binder that
  F* puts in the proof context of `e` itself, so there is nothing to name.
  `with h. e` is rejected with a message saying so.
- `Classical.move_requires*` no longer applies to a lemma that has *no*
  `requires` clause — such a lemma simply has no `squash` binder to move.
  Nor is it wanted: `Lemma (ensures Q)` is now literally `Tot (squash Q)`, which
  is what `Classical.forall_intro*` expects, so the lemma can be passed
  directly. Several vacuous `move_requires` wrappers in ulib were deleted.
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
- **Accepted regression:** a lemma stated point-free over a function that has a
  `requires` (`ensures (inj (f x))`, where `f x` is a partial application
  awaiting the squash binder) is eta-expanded at each use, and two eta-expansions
  of the same term are two distinct closures to the solver, so the lemma's
  conclusion no longer matches the goal. Removing the `requires` in favour of a
  refinement on the argument's own type removes the eta-expansion and the
  problem: this is what `ASN1.Spec.Sequence` and `ASN1.Spec.Any` do.
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

- **Extraction ABI.** A `#(squash P)` binder on a *runtime* function extracts to
  an extra `unit` argument (`let f (sq : unit) (x : Obj.t) = ...`). This is
  accepted, and the blast radius turned out to be one golden file — most
  `requires` clauses are on lemmas, which are erased entirely, or on binders that
  were already refined. Teaching extraction to erase squash-typed implicit
  binders would recover the ABI, and is left as a follow-up.
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

`make 1`, `make 2`, `make 3`, then `make test` (which covers `tests`,
`examples` and `doc`, at stage 3, with Pulse), plus `boot-diff`, `test-2-bare`,
`stage2-unit-tests` and `fsharp-all` — all green, with caches wiped so the run
is honest. Note that test `.checked` files live in `_cache` as well as
`_output`; wiping only the latter is what let several failures hide.

`ci` already runs stage 3, `examples` and `doc` via `_test`, so it needed no
change.

Beyond `ci`, EverParse's `fstar2` branch verifies end to end against this
compiler, after the downstream edits catalogued above (one `move_requires`
removal, a handful of ascriptions and explicit implicit arguments, and four
rlimit bumps). The A/B baseline build with EverParse's pinned toolchain reported
zero errors, so that catalogue is the complete list of differences this PR makes
to a large external codebase.
