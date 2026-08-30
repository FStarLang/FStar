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
  comp_univs  : universes;
  effect_name : lident;
  result_typ  : typ;
  flags       : list cflag;
}
and comp' = | Comp of comp_typ
```

A computation type is now a label and a result type. Obligations live in
`guard_t`, where they were always meant to live.

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

### The SMT encoding is unchanged

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
`cache_version_number` 93 → 94 is mandatory — and it bought the first honest
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
- **Accepted regression:** for a call through a let-bound alias, a precondition
  failure is localized to the alias rather than to the call.

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
