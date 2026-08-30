# Answers to the regression questions

Each question below was answered *empirically*: the annotation was **reverted**
and the tree rebuilt (`make -j$(nproc) -k 1 && ... 2 && ... 3`).  Whatever
passed has been reverted for good; whatever failed was root-caused.

Nine of the fourteen turned out to be unnecessary.  They were written at
intermediate points of a long commit series and never re-tested once the later
commits landed -- in particular the `bind_cases` "take the branches' result
type" rule and the fix in `tc_args` that instantiates a trailing `squash`
implicit when the callee's computation type is effectful.  They are now gone.

| # | Item | Verdict |
|---|------|---------|
| 1 | `introduce _ ==> _` wildcards (4 sites) | **reverted** |
| 2 | `TermEq.co` explicit implicits | **kept** -- genuine, see below |
| 3 | match-postcondition ascription in `faithful_lemma` | **reverted** |
| 4 | `ReflexiveTransitiveClosure` explicit arguments | **reverted** |
| 5 | `move_requires` no longer needed | explanation only |
| 6 | `<: Tac a` in `PatternMatching` | **reverted** |
| 7 | `l_False` instead of `False` | **reverted** |
| 8 | `op_exists_Star` eta-expansion | **reverted** |
| 9 | `is_frame_preserving_only_ghost`'s strengthened `ensures` | **reverted** -- it was only a proof optimization |
| 10 | `lift_erased`'s erased-pair split | **kept** -- genuine |
| 11 | `PulseCore.Semantics` `<|` removal | **reverted** |
| 12 | `Seq.init_ghost #t` | **kept** -- genuine |
| 13 | `SZ.v 0sz` instead of `0` | **reverted** |
| 14 | `(SZ.v n <: nat) == cap` | **kept** -- genuine, but there is an existing fix |

The four that survive fall into exactly **two** root causes, both direct and
predictable consequences of moving specifications out of `comp_typ`:

* **A specification is now part of a type, so it participates in unification.**
  `Lemma (ensures Q)` used to be `unit`-returning with `Q` in the comp's
  postcondition; it is now `Tot (squash Q)`.  Passing such a proof where
  `squash (... ?u ...)` is expected therefore *solves* `?u` from the lemma's
  statement, where previously the unifier saw only `unit` and left `?u` to be
  determined by the expected result type.  (Q2, and the second half of Q10.)

* **`Pure`/`Ghost` with an `ensures` now returns a refined type.**
  `val v (x:t) : Pure nat (ensures fun y -> fits y)` used to have result type
  `nat`; it now has result type `y:nat{fits y}`.  Any implicit solved from such
  a result picks up the refinement.  (Q12, Q14.)

---

## Q1 -- "Why do we have to now annotate here?" (`introduce _ ==> _`)

`ulib/FStar.FiniteSet.Base.fst`, `pulse/lib/core/PulseCore.Heap.fst`,
`pulse/lib/core/PulseCore.IndirectionTheoryActions.fst`,
`pulse/lib/pulse/lib/Pulse.Lib.PCM.Map.fst`.

**Answer: we don't.**  All four wildcards were restored and all four modules
verify.  The annotations dated from a point where the goal of an `introduce`
was not yet reaching the sub-proof; that was fixed later in the series and the
workarounds were simply never re-tested.

One genuinely new thing in this area, which is worth knowing but is not what
the diff above was about: **`introduce` and `eliminate` no longer bind a name
for the hypothesis.**  `introduce p ==> q with h. e` is now rejected with

    'introduce' and 'eliminate' no longer bind names for hypotheses;
    write 'with e' instead of 'with h. e'.  The hypothesis is available
    in the proof context of e.

because the hypothesis is now an implicit `squash` binder that F* introduces
into the proof context itself rather than a value the user can name.

---

## Q2 -- "What changed in type inference that requires this annotation now?" (`TermEq.co`)

**Answer: this one is real, and it is the clearest example of the first root
cause above.**  The annotation stays.

`co` (`ulib/FStar.Reflection.TermEq.fst:88`) has implicits `#rb #xb #yb` that
occur only in its *second* argument's type and in its result type:

```fstar
val co (#a #b:Type) (#ra:...) (#rb:...) (#xa #ya:a) (#xb #yb:b)
       (c : cmpres' ra xa ya)
       (_ : squash (ra xa ya <==> rb xb yb))
     : cmpres' rb xb yb
```

and it is applied at `bridge_opt_term x1 x2`, whose statement mentions the
**ghost** `denote_opt_term`.

* *Before.*  `bridge_opt_term x1 x2 : Lemma (...)` had result type `unit`; the
  statement lived in the comp's postcondition.  Checking it against the formal
  type `squash (ra xa ya <==> rb xb yb)` was a subtyping obligation
  (`unit <: _:unit{...}`) discharged by SMT, and gave the unifier nothing.
  `?rb ?xb ?yb` survived as uvars and were solved from the *expected result
  type* `cmpres' peq p1 p2`, i.e. `?xb := p1`.

* *Now.*  The statement is the result type.  Arguments are checked
  left-to-right, before the result type ever meets the expected type, so
  `squash A <: squash B` is a rigid-rigid application with matching heads, the
  unifier decomposes it, and it solves
  `?rb := eq2`, `?xb := denote_opt_term x1`, `?yb := denote_opt_term x2`.

Because `denote_opt_term` is `GTot`, the elaborated application acquires those
ghost terms as implicit arguments and the whole application becomes `GTot` --
which is why the failure is an *effect* mismatch (Error 34, "effect GTot ... is
not compatible with ... effect Tot") and not a type mismatch.  Minimal repro:

```fstar
assume val teq    : int -> int -> prop
assume val denote : int -> GTot int
assume val co (#b:Type) (#rb : b -> b -> prop) (#xb #yb : b)
              (c : int) (_ : squash (teq 0 0 <==> rb xb yb)) : y:int{rb xb yb}
assume val bridge (o1 o2 : int) : Lemma (teq 0 0 <==> denote o1 == denote o2)

let c5 (p1 p2:int) : Tot (y:int{denote p1 == denote p2}) = co 0 (bridge p1 p2)
//                                                         ^ Error 34: effect GTot
```

`--dump_module` confirms the solution:
`co #int #(eq2 #int) #(denote p1) #(denote p2) 0 (bridge p1 p2)`.

**Possible fixes, none of them local -- proposed as follow-ups.**

1. Check proof-irrelevant (`squash`-typed) arguments *after* relating the
   application's result type to the expected type.  A proof argument cannot
   contribute to the value of the application, so it should not get first
   claim on the implicits either.  This restores the old behaviour exactly.
2. Under `SUB`, relate `squash A` and `squash B` by unfolding to their
   refinements -- yielding the SMT obligation `A ==> B` -- instead of
   decomposing the application, at least while `B` still contains uvars.
   F* already falls back to this path; it is just tried second.  Reversing the
   order unconditionally would break inference elsewhere (a uvar *is* commonly
   solved from a `squash` argument), so it would have to be conditional.
3. Do not let a ghost *implicit* solution taint an application when the binder
   occurs only in specifications.  The most principled but by far the largest.

Until then the eight-implicit annotation is the cheapest fix, and the comment
in the source now states the confirmed cause.

---

## Q3 -- "Needing to annotate the postcondition of a match is a regression" (`faithful_lemma`)

**Answer: agreed, and it is gone.**  Both `let aux : squash (...) = match ...`
blocks were replaced by the original bare `(match tacopt1, tacopt2 with ...)`,
and the shadowed `ta1`/`ta2` renaming was undone.  `FStar.Reflection.TermEq`
verifies.  The `bind_cases` rule that takes a match's result type from its
branches, together with the expected type still being pushed into each branch,
makes the ascription unnecessary.

---

## Q4 -- "What happened here? Why do we need to annotate now?" (`ReflexiveTransitiveClosure`)

**Answer: we don't.**  `nonempty_intro (Closure x y z (nonempty_elim _) (nonempty_elim _))`
is restored -- no `#a #r`, no explicit `_closure r x y` arguments -- and the
module verifies.

---

## Q5 -- "Many instances of no longer needing `move_requires`.  Explain."

This is not "`move_requires` became unnecessary".  It is sharper than that:
**`move_requires` no longer *applies* to a lemma that has no `requires`
clause -- and no longer needs to.**

`CE.cm`'s `commutativity` field has no precondition:

```fstar
commutativity : (x:a -> y:a -> Lemma ((x `mult` y) `EQ?.eq eq` (y `mult` x)))
```

* *Before*, every `Lemma` carried a `comp_pre` field, defaulting to `l_True`.
  `move_requires_2`'s argument type `x:a -> y:b x -> Lemma (requires p x y) (ensures q x y)`
  therefore matched it with `?p := l_True`, so wrapping a precondition-free
  lemma was well-typed -- if redundant.  And `forall_intro_2` had to compare
  two `PURE` computation types whose postconditions were *thunked*
  (`fun () -> fun _ -> ...`, the hack from #57), which is why passing the field
  directly did not always work and the `move_requires` wrapper was reached for.

* *Now*, a precondition is a trailing implicit binder, and a lemma without a
  precondition simply does not have one.  So `move_requires_2` no longer
  applies:

  ```
  - Expected type   x: _ -> y: _ x -> Lemma (requires ?u x y) (ensures ?v x y)
    but cm.commutativity has type
                    x: c -> y: c -> Lemma (ensures eq.eq (cm.mult x y) (cm.mult y x))
  ```

  and it is not wanted, because `cm.commutativity` now *is* literally
  `x:c -> y:c -> Tot (squash (...))`, which is exactly `forall_intro_2`'s
  expected `x:a -> y:b x -> Lemma (p x y)` modulo the pattern unification
  `?p x y =?= eq.eq (cm.mult x y) (cm.mult y x)`.  No thunk to see through.

`move_requires` is alive and well for lemmas that *do* have a precondition;
it is only the vacuous uses that had to go.  This is a user-visible change and
is now listed as such in `PR.md`.

---

## Q6 -- "How come we need the `<: Tac a` annotation now?" (`PatternMatching`)

**Answer: we don't.**  Both ascriptions and the added parentheses were removed
and `FStar.Tactics.PatternMatching` verifies.  Same story as Q3: the match's
result type was momentarily not reaching the branches.

---

## Q7 -- "Why can't we write this as just `False` instead of `l_False`?"

**Answer: we can, and it now does.**  `admit` is back to

```fstar
assume val admit: #a: Type -> unit -> Tot (_: a{False})
```

`False` in term position is desugared straight to `Prims.l_False`
(`ToSyntax.fst:1160`), so the two spellings are the same term.  The `l_False`
was an artifact of an intermediate state of `Prims.fst` and nothing more.

While in the area, the comment above `effect Pure` was rewritten.  The old one
claimed a `requires` on an effect abbreviation is "conjoined with the one at
the use site", which is false: `ToSyntax.fst:2920-2934` rejects a `requires` on
an abbreviation outright, because it would have to become an implicit binder on
the *arrow* whose codomain the abbreviation is used at, and an abbreviation has
no arrow of its own.

---

## Q8 -- "Why the eta expansion here and elsewhere?" (`op_exists_Star`)

**Answer: no reason any more.**  `let op_exists_Star = op_exists_Star` is
restored and `Pulse.Lib.Core` verifies.  (The `conv_squash` / `bridge_exists`
helpers in the same file are a different matter and stay: they transport a fact
between two point-free re-exports by *conversion* rather than by SMT, which is
independent of this refactor.)

---

## Q9 -- "Is this just a proof optimization to reduce ifuel?  Or is it necessary?" (`is_frame_preserving_only_ghost`)

**Answer: it was just a proof optimization, and it is reverted.**  The `ensures`
is back to the original one-liner

```fstar
  (ensures (dsnd (f h)).concrete == h.concrete)
```

Verified by isolating the two changes: with the *original* `ensures` and the
new `lift_erased` body (Q10), `PulseCore.Heap2` verifies; the strengthened
postcondition contributes nothing.  It had been bundled together with Q10
during debugging and never separated.

---

## Q10 -- "Why this change?" (`lift_erased`'s `erased (a & H.heap)` split)

**Answer: this one is necessary.**  It is the same root cause as Q2, seen from
the other side.

`is_frame_preserving_only_ghost`'s conclusion is stated about
`dsnd (f h)`.  Previously that conclusion arrived as a *postcondition* of the
lemma call and was assumed at the program point; the local
`let (| x, hh' |) = ff h in ... Ghost.hide (x, Ghost.reveal hh'.ghost)` was
enough to connect it to `gg`.  Now the conclusion is a refinement on the
lemma's `squash` result, and relating `fst gg` / `snd gg` back to
`dfst (ff h)` / `(dsnd (ff h)).ghost` has to go through the tuple projectors on
an `erased` pair -- which needs `ifuel` that this module does not have.
Keeping the two components as separate `erased` bindings avoids the pair
entirely.

The same rewrite is needed in `lift_heap_pre_action_ghost` a few lines below,
and reverting only one of the two reproduces the failure at the other.
Both sites carry a comment.

---

## Q11 -- "Why do we need an annotation here now?" (`PulseCore.Semantics` `<|`)

**Answer: we don't.**  The `ST.weaken <| ST.bind (a.step frame) <| (fun x -> ...)`
spelling is restored and `PulseCore.Semantics` verifies.

---

## Q12 -- "Why do we need an annotation here now?" (`Seq.init_ghost #t`)

**Answer: this one is necessary**, and it is the second root cause: a
`Pure`/`Ghost` with an `ensures` now *returns a refined type*.

```fstar
val mk_fraction (#t: Type0) (td: typedef t) (x: t) (p: perm) : Ghost t
  (requires (fractionable td x))
  (ensures (fun y -> p <=. 1.0R ==> fractionable td y))
```

used to have result type `t`; it now has result type
`y:t{p <=. 1.0R ==> fractionable td y}`.  `Seq.init_ghost`'s `#a` is solved
from the lambda's result, so without the annotation `#a` becomes that refined
type and the declared `Ghost (Seq.seq t)` no longer matches:

```
  - Expected type FStar.Seq.Base.seq t
    got type      FStar.Seq.Base.seq (_: t{p <=. 1.0R ==> fractionable #t td _})
```

`#t` pins it.  See Q14 for the general remedy.

---

## Q13 -- "This is odd, writing `SZ.v 0sz` rather than `0`.  Why?" (`HashTableChained`)

**Answer: it is odd, and it is gone.**  Both `SZ.v 0sz` occurrences are back to
`0` (and the extra `range_rebound` call that had been added alongside is
removed again); `Pulse.Lib.HashTableChained` verifies.

---

## Q14 -- "Needing to annotate in polymorphic equality.  What can we do to improve it?"

**Answer: there is already a mechanism for exactly this, and it works.**

The cause is the same as Q12.  `FStar.SizeT.v` is declared

```fstar
val v (x: t) : Pure nat (requires True) (ensures (fun y -> fits y))
```

so `SZ.v n` used to have type `nat` and now has type `y:nat{fits y}`.
`eq2`'s type implicit is solved from the first argument, so `SZ.v n == cap`
elaborates to `eq2 #(y:nat{fits y}) (SZ.v n) cap` and demands `fits cap`, which
is not provable for an arbitrary `cap:nat`:

```
  - Failed to prove: FStar.SizeT.fits cap
```

`Prims.fst` already declares

```fstar
assume val eq2 (#[@@@unrefine] a: Type) (x: a) (y: a) : prop
```

The `unrefine` binder attribute tells the typechecker to strip refinements when
instantiating that implicit (`Env.uvar_meta_for_binder` ->
`new_implicit_var_aux ... should_unrefine`).  It is gated behind
`--ext __unrefine` and is documented in `Prims.fst` as experimental.  It fixes
this case precisely:

```fstar
let f (n:SZ.t) (cap:erased nat) : prop = (SZ.v n == cap)
//   without the flag:  Failed to prove: FStar.SizeT.fits _
//   with --ext __unrefine:  Verified module
```

**Recommendation.**  This refactor makes refined result types the norm rather
than the exception, which strengthens the case for promoting `unrefine` from an
experimental flag to the default -- at least for `eq2`, `( = )` and `( <> )`,
which already carry the attribute.  That is a decision with a repo-wide blast
radius (it changes which type polymorphic equality is taken at, everywhere), so
it is deliberately *not* bundled into this PR; the four `(SZ.v n <: nat)`
ascriptions stay for now and this note records the intended fix.

---

## Appendix: the questions as originally asked

Why do we have to now annotate here?

--- a/ulib/FStar.FiniteSet.Base.fst
+++ b/ulib/FStar.FiniteSet.Base.fst
@@ -175,7 +175,7 @@ let length_zero_lemma ()
     with assert (feq s emptyset);
     introduce s == emptyset ==> cardinality s = 0
     with assert (set_as_list s == []);
-    introduce cardinality s <> 0 ==> _
+    introduce cardinality s <> 0 ==> (exists x. mem x s)
     with introduce exists x. mem x s
             with (Cons?.hd (set_as_list s))
             and  ())

diff --git a/pulse/lib/core/PulseCore.Heap.fst b/pulse/lib/core/PulseCore.Heap.fst
index e83c6f51e6..b827d732c8 100644
--- a/pulse/lib/core/PulseCore.Heap.fst
+++ b/pulse/lib/core/PulseCore.Heap.fst
 
@@ -1152,7 +1152,7 @@ let extend_full_heap_with (h: full_heap) (c: cell {full_cell c}) :
     } =
   let h' = Seq.snoc h (Some c) in
   introduce forall a. contains_addr h' a ==> full_cell (select_addr h' a) with
-    introduce _ ==> _ with
+    introduce contains_addr h' a ==> full_cell (select_addr h' a) with
       if a = ctr h then () else
         assert select_addr h' a == select_addr h a;
   h'

diff --git a/pulse/lib/core/PulseCore.IndirectionTheoryActions.fst b/pulse/lib/core/PulseCore.IndirectionTheoryActions.fst
index 9de4069705..c2fcdb2564 100644
--- a/pulse/lib/core/PulseCore.IndirectionTheoryActions.fst
+++ b/pulse/lib/core/PulseCore.IndirectionTheoryActions.fst
@@ -83,7 +83,7 @@ let pin_frame (p:pm_slprop) (frame:slprop)
   : Lemma (B.is_affine_mem_prop fr)
   = introduce forall s0 s1.
       fr s0 /\ B.disjoint_mem s0 s1 ==> fr (B.join_mem s0 s1)
-    with introduce _ ==> _
+    with introduce fr s0 /\ B.disjoint_mem s0 s1 ==> fr (B.join_mem s0 s1)
     with
       update_timeless_mem_join m1 s0 s1
   in

diff --git a/pulse/lib/pulse/lib/Pulse.Lib.PCM.Map.fst b/pulse/lib/pulse/lib/Pulse.Lib.PCM.Map.fst
index 79638eb9fe..616b821ffe 100644
--- a/pulse/lib/pulse/lib/Pulse.Lib.PCM.Map.fst
+++ b/pulse/lib/pulse/lib/Pulse.Lib.PCM.Map.fst
@@ -265,9 +265,11 @@ let lift_frame_preservation #a (#k:eqtype) (p:pcm a)
          (op p' m0 frame == full_m0 ==>
           op p' m1 frame == full_m1)
       with (
-        introduce _ /\ _
+        introduce composable p' m1 frame
+              /\ (op p' m0 frame == full_m0 ==> op p' m1 frame == full_m1)
         with ()
-        and ( introduce _ ==> _
+        and ( introduce (op p' m0 frame == full_m0)
+                    ==> (op p' m1 frame == full_m1)
               with (
                   assert (compose_maps p m1 frame `Map.equal` full_m1)

What changed in type inference that requires this annotation now?

index b12c644981..e1f74b4452 100644
--- a/ulib/FStar.Reflection.TermEq.fst
+++ b/ulib/FStar.Reflection.TermEq.fst
@@ -827,7 +827,10 @@ and pat_cmp p1 p2 =
     co (const_cmp x1 x2) ()
 
   | Pat_Dot_Term x1, Pat_Dot_Term x2 ->
-    co (opt_dec_cmp' p1 p2 term_cmp x1 x2) (bridge_opt_term x1 x2)
+    (* [co]'s [#xb #yb] must be pinned to [p1] and [p2].  Left to inference they
+       are solved from the second argument's type instead, which mentions the
+       ghost [denote_opt_term], and that makes the whole application [GTot]. *)
+    co #_ #_ #_ #peq #_ #_ #p1 #p2 (opt_dec_cmp' p1 p2 term_cmp x1 x2) (bridge_opt_term x1 x2)


Needing to annotate the postcondition of a match is a regression:

     (***)term_eq_Tv_Match t1 t2 sc1 sc2 o1 o2 brs1 brs2;
     ()
 
-  | Tv_AscribedT e1 t1 tacopt1 eq1, Tv_AscribedT e2 t2 tacopt2 eq2 ->
+  | Tv_AscribedT e1 ta1 tacopt1 eq1, Tv_AscribedT e2 ta2 tacopt2 eq2 ->
     faithful_lemma e1 e2;
-    faithful_lemma t1 t2;
-    (match tacopt1, tacopt2 with | Some t1, Some t2 -> faithful_lemma t1 t2 | _ -> ());
+    faithful_lemma ta1 ta2;
+    let aux : squash (defined (opt_dec_cmp' t1 t2 term_cmp tacopt1 tacopt2)) =
+      match tacopt1, tacopt2 with
+      | Some x1, Some x2 -> faithful_lemma x1 x2
+      | _ -> ()
+    in
     ()
 
   | Tv_AscribedC e1 c1 tacopt1 eq1, Tv_AscribedC e2 c2 tacopt2 eq2 ->
     faithful_lemma e1 e2;
     faithful_lemma_comp c1 c2;
-    (match tacopt1, tacopt2 with | Some t1, Some t2 -> faithful_lemma t1 t2 | _ -> ());
+    let aux : squash (defined (opt_dec_cmp' t1 t2 term_cmp tacopt1 tacopt2)) =
+      match tacopt1, tacopt2 with
+      | Some x1, Some x2 -> faithful_lemma x1 x2
+      | _ -> ()
+    in
     ()

What happened here? Why do we need to annotate now?

diff --git a/ulib/FStar.ReflexiveTransitiveClosure.fst b/ulib/FStar.ReflexiveTransitiveClosure.fst
index 61d349aa14..0e85579e72 100644
--- a/ulib/FStar.ReflexiveTransitiveClosure.fst
+++ b/ulib/FStar.ReflexiveTransitiveClosure.fst
@@ -53,7 +53,8 @@ val closure_transitive: #a:Type u#a -> r:binrel u#a a -> Lemma (transitive (_clo
 let closure_transitive #a r =
   introduce forall x y z. _closure0 r x y /\ _closure0 r y z ==> _closure0 r x z with
   introduce _ ==> _ with
-  nonempty_intro (Closure x y z (nonempty_elim _) (nonempty_elim _))
+  nonempty_intro (Closure #a #r x y z (nonempty_elim (_closure r x y))
+                                      (nonempty_elim (_closure r y z)))


There are many instances of no longer needing move_requires. This is an
improvement ... but I don't understand how it works. Explain

diff --git a/ulib/FStar.Seq.Permutation.fst b/ulib/FStar.Seq.Permutation.fst
index fd5603db9c..de437a127c 100644
--- a/ulib/FStar.Seq.Permutation.fst
+++ b/ulib/FStar.Seq.Permutation.fst
@@ -491,12 +491,12 @@ let rec foldm_snoc_perm #a #eq m s0 s1 p
 let cm_associativity #c #eq (cm: CE.cm c eq)
   : Lemma (forall (x y z:c). {:pattern (x `cm.mult` y `cm.mult` z)}
               (x `cm.mult` y `cm.mult` z) `eq.eq` (x `cm.mult` (y `cm.mult` z)))
-  = Classical.forall_intro_3 (Classical.move_requires_3 cm.associativity)
+  = Classical.forall_intro_3 cm.associativity
 
 let cm_commutativity #c #eq (cm: CE.cm c eq)
   : Lemma (forall (x y:c). {:pattern (x `cm.mult` y)}
               (x `cm.mult` y) `eq.eq` (y `cm.mult` x))
-  = Classical.forall_intro_2 (Classical.move_requires_2 cm.commutativity)
+  = Classical.forall_intro_2 cm.commutativity

How come we need the `<: Tac a` annotation now?

diff --git a/ulib/FStar.Tactics.PatternMatching.fst b/ulib/FStar.Tactics.PatternMatching.fst
index 8574b60db2..861abe7211 100644
--- a/ulib/FStar.Tactics.PatternMatching.fst
+++ b/ulib/FStar.Tactics.PatternMatching.fst
@@ -442,14 +442,14 @@ let rec solve_mp_for_single_hyp #a
   | h :: hs ->
     or_else // Must be in ``Tac`` here to run `body`
       (fun () ->
-         match interp_pattern_aux pat part_sol.ms_vars (type_of_binding h) with
-         | Failure ex ->
-           fail ("Failed to match hyp: " ^ (string_of_match_exception ex))
-         | Success bindings ->
-           let ms_hyps = (name, h) :: part_sol.ms_hyps in
-           body ({ part_sol with ms_vars = bindings; ms_hyps = ms_hyps }))
+         (match interp_pattern_aux pat part_sol.ms_vars (type_of_binding h) with
+          | Failure ex ->
+            fail ("Failed to match hyp: " ^ (string_of_match_exception ex))
+          | Success bindings ->
+            let ms_hyps = (name, h) :: part_sol.ms_hyps in
+            body ({ part_sol with ms_vars = bindings; ms_hyps = ms_hyps })) <: Tac a)
       (fun () ->
-         solve_mp_for_single_hyp name pat hs body part_sol)
+         solve_mp_for_single_hyp name pat hs body part_sol <: Tac a)


Why can't we write this as just False instead of l_False?

assume
-val admit: #a: Type -> unit -> Admit a
+val admit: #a: Type -> unit -> Tot (_: a{l_False})

I didn't understand why we have a change in behavior that requires the eta expansion here and elsewhere:

diff --git a/pulse/lib/core/Pulse.Lib.Core.fst b/pulse/lib/core/Pulse.Lib.Core.fst
index aa15eb80eb..4060e8915b 100644
--- a/pulse/lib/core/Pulse.Lib.Core.fst
+++ b/pulse/lib/core/Pulse.Lib.Core.fst
@@ -48,7 +48,10 @@ let pure = pure
 let timeless_pure p = Sep.timeless_pure p
 let ( ** ) = op_Star_Star
 let timeless_star p q = Sep.timeless_star p q
-let op_exists_Star = op_exists_Star
+(* Eta-expanded so that the SMT encoding relates [Pulse.Lib.Core.op_exists_Star]
+   to [Sep.op_exists_Star] *applied*; the point-free definition only related the
+   two function values, which SMT cannot use. *)
+let op_exists_Star #a p = Sep.op_exists_Star #a p


Why did this change?

@@ -433,7 +437,12 @@ let is_frame_preserving_only_ghost
     (h:full_hheap fp)
 : Lemma 
   (requires is_frame_preserving ONLY_GHOST f)
-  (ensures (dsnd (f h)).concrete == h.concrete)
+  (ensures (
+    let (| x, hh' |) = f h in
+    hh'.concrete == h.concrete /\
+    hh' == { h with ghost = hh'.ghost } /\
+    interp (fp' x) ({ h with ghost = hh'.ghost }) /\
+    full_heap_pred ({ h with ghost = hh'.ghost })))


Is this just a proof optimization to reduce ifuel? Or is it necessary to write it this way now?

let lift_erased
 : action #mut pre a post
 = let g : refined_pre_action #mut pre a post =
     fun h ->
-      let gg : erased (a & H.heap) =
+      (* Keep the result's two components as separate [erased] bindings: an
+         [erased] *pair* would need the tuple projector axioms (and hence
+         [--ifuel]) to relate [fst gg] back to [dfst (reveal f h)], which is
+         where the facts below are stated. *)
+      let gx : erased a =

Why this change?

--- a/pulse/lib/core/PulseCore.Semantics.fst
+++ b/pulse/lib/core/PulseCore.Semantics.fst
@@ -272,9 +272,9 @@ let raise_action
       pre = a.pre;
       post = F.on_dom _ (fun (x:U.raise_t u#a u#(max a b) t) -> a.post (U.downgrade_val x));
       step = (fun frame ->
-               ST.weaken <|
-               ST.bind (a.step frame) <|
-               (fun x -> ST.return <| U.raise_val u#a u#(max a b) #_ #U.raisable_inst x))
+               ST.weaken
+                 (ST.bind (a.step frame)
+                          (fun x -> ST.return (U.raise_val u#a u#(max a b) #_ #U.raisable_inst x))))
    }

Why do we need an annotation here now?

diff --git a/pulse/lib/pulse/c/Pulse.C.Types.Array.fsti b/pulse/lib/pulse/c/Pulse.C.Types.Array.fsti
index eb1962e525..28e8787a23 100644
--- a/pulse/lib/pulse/c/Pulse.C.Types.Array.fsti
+++ b/pulse/lib/pulse/c/Pulse.C.Types.Array.fsti
@@ -993,7 +993,7 @@ let fractionable_seq (#t: Type) (td: typedef t) (s: Seq.seq t) : prop =
 let mk_fraction_seq (#t: Type) (td: typedef t) (s: Seq.seq t) (p: perm) : Ghost (Seq.seq t)
   (requires (fractionable_seq td s))
   (ensures (fun _ -> True))
-= Seq.init_ghost (Seq.length s) (fun i -> mk_fraction td (Seq.index s i) p)
+= Seq.init_ghost #t (Seq.length s) (fun i -> mk_fraction td (Seq.index s i) p)

This is odd, writing SZ.v 0sz rather than 0. Why?

diff --git a/pulse/lib/pulse/lib/Pulse.Lib.HashTableChained.fst b/pulse/lib/pulse/lib/Pulse.Lib.HashTableChained.fst
index 8ca6a189a4..3578fdc615 100644
--- a/pulse/lib/pulse/lib/Pulse.Lib.HashTableChained.fst
+++ b/pulse/lib/pulse/lib/Pulse.Lib.HashTableChained.fst
@@ -2314,7 +2314,7 @@ ensures is_ht h empty_pmap FS.emptyset
   rewrite (V.pts_to buckets final_ptrs) as (V.pts_to h.buckets final_ptrs);
   rewrite (B.pts_to count 0sz) as (B.pts_to h.count 0sz);
   
-  range_rebound (bucket_at final_ptrs final_contents) 0 (SZ.v initial_capacity) 0 (SZ.v h.capacity);
+  range_rebound (bucket_at final_ptrs final_contents) (SZ.v 0sz) (SZ.v initial_capacity) 0 (SZ.v h.capacity);
   fold (is_ht h empty_pmap FS.emptyset);
   h
 }

Ah, needing to annotate in polymorphic equality. I was expecting we would need this in some places. What can we do to improve it?

@@ -732,7 +732,7 @@ fn size (#t:Type0) {| total_order t |} (pq:pqueue t) (#cap:erased nat)
 fn get_capacity (#t:Type0) {| total_order t |} (pq:pqueue t) (#s0:erased (Seq.seq t)) (#cap:erased nat)
   preserves is_pqueue pq s0 cap
   returns n:SZ.t
-  ensures pure (SZ.v n == cap)
+  ensures pure ((SZ.v n <: nat) == cap)

diff --git a/pulse/lib/pulse/lib/Pulse.Lib.PriorityQueue.fsti b/pulse/lib/pulse/lib/Pulse.Lib.PriorityQueue.fsti
index d451cf42e7..9b766b7bee 100644
--- a/pulse/lib/pulse/lib/Pulse.Lib.PriorityQueue.fsti
+++ b/pulse/lib/pulse/lib/Pulse.Lib.PriorityQueue.fsti
@@ -64,7 +64,7 @@ fn size (#t:Type0) {| total_order t |} (pq:pqueue t) (#cap:erased nat)
 fn get_capacity (#t:Type0) {| total_order t |} (pq:pqueue t) (#s0:erased (Seq.seq t)) (#cap:erased nat)
   preserves is_pqueue pq s0 cap
   returns n:SZ.t
-  ensures pure (SZ.v n == cap)
+  ensures pure ((SZ.v n <: nat) == cap)

diff --git a/pulse/lib/pulse/lib/Pulse.Lib.ResizableVec.fst b/pulse/lib/pulse/lib/Pulse.Lib.ResizableVec.fst
index 2a3ba5a653..efe9f40bf7 100644
--- a/pulse/lib/pulse/lib/Pulse.Lib.ResizableVec.fst
+++ b/pulse/lib/pulse/lib/Pulse.Lib.ResizableVec.fst
@@ -120,7 +120,7 @@ fn len (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
 fn get_capacity (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
   preserves is_rvec v s cap
   returns n:SZ.t
-  ensures pure (SZ.v n == cap)
+  ensures pure ((SZ.v n <: nat) == cap)
 {
   unfold (is_rvec v s cap);
   with vec buf sz cap_sz. _;
diff --git a/pulse/lib/pulse/lib/Pulse.Lib.ResizableVec.fsti b/pulse/lib/pulse/lib/Pulse.Lib.ResizableVec.fsti
index e0f6b30d97..f4fad0d989 100644
--- a/pulse/lib/pulse/lib/Pulse.Lib.ResizableVec.fsti
+++ b/pulse/lib/pulse/lib/Pulse.Lib.ResizableVec.fsti
@@ -53,7 +53,7 @@ fn len (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
 fn get_capacity (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
   preserves is_rvec v s cap
   returns n:SZ.t
-  ensures pure (SZ.v n == cap)
+  ensures pure ((SZ.v n <: nat) == cap)
 