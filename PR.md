# Push the expected postcondition without putting it in the expected type

Follow-on to #4508. That PR made the postcondition push the default by folding
the expected postcondition into the expected type of a lambda's body, as a
refinement. This PR keeps the behaviour it was after — an obligation raised in
the failing sub-term's own context, at its own range — and changes how it is
carried, because a refinement in the expected type is visible to unification and
was reaching places it should not.

It also extends the push to where it actually matters (ascriptions), fixes the
two-phase path that was silently dropping it, and removes a redundant
whole-match obligation that was reporting a second, less precise error *before*
the precise one.

5 commits, 18 files, `+417 / −56`.

| | Before this PR | After |
|---|---|---|
| Where the post lives | refinement in `expected_typ` | `Env.expected_post`, a separate field |
| Visible to unification | **yes** — could solve a uvar | no — materialized only at check sites |
| Pushed at | lambdas | lambdas **and** ascriptions (`Inr` comp and `Inl` type) |
| Survives two-phase | no (phase 2 lost it via `tc_match`'s self-ascription) | yes |
| Whole-match re-proof | yes — second, less precise error first | no |
| ulib rlimit increases | 5 | 1 |

---

## 1. The postcondition should not be a type

Folding the postcondition into the expected type is observable by unification.
Concretely, this was rejected:

```fstar
assume val p : int -> prop
assume val lem (x:int) : Lemma (p x)

let no_inference_leak (b:bool) : Pure int (requires True) (ensures fun r -> p r) =
  let y = if b then 1 else 2 in
  lem y;
  y
```

The unannotated inner `let` is checked with the expected type cleared, so the
result type of its `if` is a fresh unification variable. The refined expected
type of the `let` *body* then solves that variable to `_:int{p _}`, so the second
phase re-checks the two branches of the `if` against the refinement — i.e. before
`lem y` has established it.

So the postcondition is now kept out of the type. `Env.env` gains

```fstar
expected_post : option typ
```

set only by the new `Env.set_expected_typ_and_post`, and reset by every other
setter of `expected_typ` (in particular `clear_expected_typ`), so it survives
exactly along the positions that inherit the ambient expected type: match and
`if` branches, `let` bodies, and ascriptions. The refinement is materialized
only at the point of the check, in `value_check_expected_typ` and
`comp_check_expected_typ`, and never becomes a candidate solution for a uvar.

`expected_typ_with_post` drops the refinement when the context checks the result
type by equality (`use_eq` / `use_eq_strict` — a refinement of `t` is not `t`, and
`weaken_result_typ` would call `Rel.try_teq` and fail), or when the computed
result type still mentions uvars, which is the direct guard against the case
above.

Dropping it is always sound: `check_expected_effect` raises the obligation in
full regardless. Pushing only makes it arise **earlier**, in the sub-term's own
context and at its own range.

`tests/micro-benchmarks/PushPostcondition.fst` pins both halves — that the
obligation lands in tail position, and that recording it does not perturb
inference. Besides `no_inference_leak` above it covers the same shape through an
ascription, a lambda passed as an argument, an inferred implicit, and a
`$`-binder (which forces an equality check, so no refinement may appear there).

## 2. Ascriptions are where the push actually matters

The push was only performed for lambdas. But the desugarer turns

```fstar
let f x : C = body
```

into `fun x -> (body <: C)`, so for an *ordinary annotated definition* the
postcondition never reached the body at all. `Tm_ascribed` nodes with a
computation-type ascription now go through the same `set_expected_typ_of_comp`.

Type ascriptions (`Inl`) matter too, for a subtler reason. `tc_match` ascribes
its own output with `Tm_ascribed (match, Inl cres.res_typ)`. So for a definition
whose type comes from a `val` declaration, the **second phase** sees a type
ascription where the first saw a bare match — and the old code called
`set_expected_typ_maybe_eq`, which resets `expected_post`. The postcondition was
therefore dropped on every second phase, which is why `val`-declared definitions
showed no improvement at all. `set_expected_typ_of_ascription` carries it
through when the ascribed type is the one the context already expects.

## 3. A match should take the result type its branches established

`bind_cases` is the one place in the checker where a result type is **chosen**
rather than propagated: a match has no single subterm to take its type from, so
it is handed one. Every other combinator threads through the type of what it is
built from. (I grepped for other sites that form a result type from the expected
type; there are none — so this is the only place that needed attention.)

Handing it the plain expected type discards whatever the branches have in
common, and makes the match prove again what each branch already proved. With a
postcondition that meant the obligation was raised twice: once per branch, and
once for the whole match — and since errors come out in the order they are
raised, the imprecise whole-match error was printed **first**. That was the
remaining half of the localization problem.

The rule is now stated without reference to postconditions:

> When the branches agree on a result type, and it is scoped outside the match,
> it is a result type for the match, and we take theirs.

A postcondition-refined type is preserved because all the branches carry it, not
because it is looked for. Their result types are only *read*, never set, so
nothing is claimed of a branch it did not establish. (Assuming the refined type
would be unsound — a branch may legitimately have dropped it.) An `Env.closed`
check makes it safe to take a branch's type directly.

---

## Considered and rejected: carrying the obligation in the postcondition

The obvious systematic alternative is to record the discharged fact in the
computation type's **postcondition** rather than as a refinement of the result
type. That is the compositional channel — `bind` quantifies over posts,
`mk_conjunction` conjoins them — so the fact reaches the enclosing computation
with no help from `bind_cases`, and the whole of §3 becomes unnecessary. It also
removes the `use_eq` guard, the uvar-groundness heuristic, and the ascription
refinement-matching.

I implemented it (`return_value_with_post` + `strengthen_with_post` in
`TypeChecker.Util`) and measured it. **It does not work**, for a reason worth
recording:

> The postcondition composes but cannot be *discharged*. The enclosing check has
> no way to see the obligation was already met, so the fact must be carried in
> the post at every tail position *and* the obligation re-raised in the pre at
> each level.

The accumulated context grew enough to lose two ulib proofs outright —
`FStar.UInt.index_to_vec_ones` and `FStar.Seq.Sorted.intro_sorted_pred`. I dumped
the failing context for the first and confirmed every needed hypothesis was
present; Z3 simply could not find it among the vacuous `cond ==> P` copies.

A refinement of the result type, by contrast, is absorbed **syntactically** by
`weaken_result_typ`'s equality short-circuit, so the enclosing obligation costs
zero SMT. *Absorbability*, not compositionality, is the property that decides
this — which is why the type is the right channel here even though the post is
the compositional one.

---

## Diagnostics

The flagship case:

```fstar
val declared : b:bool -> Pure int (requires True) (ensures fun r -> p r)
let declared b = if b then (lem 1; 1) else 2
```

Before the feature (nightly-2026-08-17), the whole body is blamed, the goal is a
metavariable, and the match itself is dragged into the context:

```
* Error 19 at D.fst(6,17-6,44):                <- the entire `if ... else 2`
  - Assertion failed
  - Failed to prove: D.p _
  - In context:
      b: Prims.bool
      uu___: Prims.int
      (b = true ==> b == true /\ D.p 1) /\
      _ == (match b with | true -> 1 | _ -> 2)
```

Now:

```
* Error 19 at PostconditionLocalization.fst(23,28-23,29):     <- just the `2`
  - Subtyping check failed
  - Expected type _: Prims.int{p _} got type Prims.int
  - Failed to prove: PostconditionLocalization.p 2
  - In context:
      b: Prims.bool
      ~(b = true)
```

Note this particular shape — a `val`-declared definition — was *not* fixed by
PR #4508 alone. That PR pushes at the lambda, but `tc_match` ascribes its own
output with the match's result type, so the second phase saw an `Inl` ascription
and `set_expected_typ_maybe_eq` reset the postcondition. §2 is what makes it
work.

Existing goldens move the same way — the range narrows to the offending
sub-term, and the context loses the spurious extra `uu___: Prims.unit` that came
from stating the obligation over the whole body:

```
 * Info at WPExtensionality.fst(61,3-61,34):      ->   (61,31-61,33)
-  - Assertion failed
-  - In context:
-      uu___: Prims.unit
-      uu___: Prims.unit
+  - Subtyping check failed
+  - Expected type _: Prims.unit{Prims.l_False} got type Prims.unit
+  - In context: uu___: Prims.unit
```

`tests/error-messages/PostconditionLocalization.fst` pins one precise error per
shape across five shapes: annotated definition, `val`-declared definition,
lambda against an expected arrow, and a three-way datatype match — plus the
`returns` case below.

## Known boundary: `match ... returns`

A match with a `returns` annotation calls `Env.clear_expected_typ` for its
branches on purpose — the annotation is there to override the expected type —
and that takes the expected postcondition with it. Such a match proves its
postcondition once, as a whole, and a failure blames the whole match.

I left this as-is rather than special-casing it: it is the same choice already
made for the expected type, and the annotation is the user saying what the type
should be. It is pinned in the golden file so the behaviour is explicit rather
than accidental, and commented at the `clear_expected_typ` site.

## Proof adjustments

Raising obligations earlier and per-branch changes query shape, so a few proofs
needed attention.

**`BinomialQueue.find_max_emp_repr_l`** — an explicit contradiction. The
non-empty branch is vacuous, but the only fact at the branch tail is
`last_key_in_keys`'s postcondition, a pattern-matching let
(`let Internal _ k _ = L.last l in ...`) that is *stuck* until
`Internal? (L.last l)` is known. That is derivable from `priq`'s refinement plus
`~(Nil? l)`, but nothing in the goal prompts unfolding `is_compact`. The added
assert is a **trigger, not information**.

Worth stating plainly: this is not an expressiveness regression. On master,
writing `assert (find_max None l == None)` at that same tail position *also*
fails. The proof was never robust there; it only worked because the obligation
was discharged elsewhere.

**rlimit increases** — 5 were needed when the feature first landed; after §2 and
§3 reshaped the obligations I rechecked each individually and **4 are no longer
needed** (`FStar.Math.Euclid`, `FStar.Matrix`, `FStar.OrdSet`,
`FStar.Reflection.TermEq`). Only `FStar.FiniteSet.Base` still needs one.

The two in `BoolRefinement` were rechecked the same way and both are still
required — `elab_open_commute'` fails at 717 without it, `rename_elab_binding_denote`
at 1072 — so they pay for the pushed per-branch obligation, not a whole-match
artifact.

## Cost

ulib solver time is unchanged: **14m59** against a 14m58 baseline. The
whole-match obligation removed in §3 roughly pays for the per-branch ones added.

## Validation

`make 1` / `clean-2 && make 2` / `clean-3 && make 3`, then all caches wiped and
`make test`, `boot-diff`, `test-2-bare`, `stage2-unit-tests`, `fsharp-all`.

Run twice: once on the branch tip, and again after merging current master —
worth doing because that merge brings in `FStar.Math.Sqrt`, a new ulib module
this feature had never seen, and an extraction change. Both runs green, zero
errors. Branch is up to date with `origin/master` (`40861db838`), so the merge
base is master itself.

## Files

- `src/typechecker/FStarC.TypeChecker.Env.{fst,fsti}` — the `expected_post` field,
  `set_expected_typ_and_post`, `expected_post`.
- `src/typechecker/FStarC.TypeChecker.TcTerm.fst` — `refine_by_post`,
  `expected_typ_with_post`, `set_expected_typ_of_comp`,
  `set_expected_typ_of_ascription`, and the `bind_cases` result-type rule.
- `tests/micro-benchmarks/PushPostcondition.fst` — tail position + no inference leak.
- `tests/error-messages/PostconditionLocalization.fst` — one error per shape,
  including the `returns` boundary.
