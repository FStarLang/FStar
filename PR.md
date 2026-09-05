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

`make 1`, `make 2`, `make 3`, then `make test` (which covers `tests`,
`examples` and `doc`, at stage 3, with Pulse), plus `boot-diff`, `test-2-bare`,
`stage2-unit-tests` and `fsharp-all` — all green, with caches wiped so the run
is honest. Note that test `.checked` files live in `_cache` as well as
`_output`; wiping only the latter is what let several failures hide.

`ci` already runs stage 3, `examples` and `doc` via `_test`, so it needed no
change.

Beyond `ci`, EverParse's `fstar2` branch verifies and extracts end to end
against this compiler, from a clean tree, after the downstream edits catalogued
above. The A/B baseline build with EverParse's pinned toolchain reported zero
errors, so that catalogue is the complete list of differences this PR makes to a
large external codebase: **30 files, +223/-100 lines**, made up of explicit
implicit arguments and type ascriptions, `assert`s restating a fact the solver
used to be handed, four small helper `Lemma`s, one `Ghost.hide`, and two rlimit
bumps. Each of the five load-bearing workarounds was re-tested against the final
compiler with the pristine source restored, and each is still required; none is
masking a bug that has since been fixed.

Kuiper is the second such run, and the same statement holds for it: 396 modules,
green from a clean tree, against a baseline of 396 green modules built with the
F* fork kuiper pins; **6 files, +21/-16 lines** of downstream difference,
catalogued above. Both downstream trees were re-verified from scratch against the
final compiler, after the last typechecker fix, not against the compiler each
regression was found on.
