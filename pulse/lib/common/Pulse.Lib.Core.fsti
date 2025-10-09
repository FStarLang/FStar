(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.Core
open FStar.Ghost
open PulseCore.FractionalPermission
open PulseCore.Observability
open FStar.PCM
module T = FStar.Tactics.V2
open Pulse.Lib.Dv {}
open FStar.ExtractAs

(* Arguments of slprops can be marked as a matching key to
   1- Make sure we do no try to use the SMT to match resources with
      different matching keys (in other words, we only use the unifier to
      match the matching keys).
   2- Indicate that we only expect a single instance of the resource for
      a given set of matching keys, so we allow the use of SMT for the rest
      of the arguments.

     val pts_to ([@@@mkey] x : ref a) (v : a) : slprop

   Then `pts_to x (a + b)` and `pts_to x (b + a)` will be matched by the
   prover by emitting an SMT query `pts_to x (a + b) == pts_to x (b +
   a)`. (Note we ask for this possibly weaker fact instead of `(a + b)
   == (b + a)`; this can be useful when the definition of the resource
   is not injective.)

   Of course, `pts_to x a` and `pts_to x a` will be matched purely by
   unification without even emitting a trivial SMT query (a == a).
*)
val mkey : unit
val no_mkeys : unit

(** This attribute allows to do ambiguous proving when calling a function. *)
val allow_ambiguous : unit

(***** begin slprop_equiv *****)

(* A full slprop. In universe 4 (currently!) *)
[@@erasable]
val slprop : Type u#4

val timeless (p: slprop) : prop

let timeless_slprop = v:slprop { timeless v }

val emp : slprop

val timeless_emp : squash (timeless emp)

val pure (p:prop) : slprop

val timeless_pure  (p:prop)
: Lemma (timeless (pure p))
        [SMTPat (timeless (pure p))]

val ( ** ) (p q:slprop) : slprop

val timeless_star (p q : slprop)
: Lemma
    (requires timeless p /\ timeless q)
    (ensures timeless (p ** q))
    [SMTPat (timeless (p ** q))]

val ( exists* ) (#a:Type) (p:a -> slprop) : slprop

val timeless_exists (#a:Type u#a) (p: a -> slprop)
: Lemma
    (requires forall x. timeless (p x))
    (ensures timeless (op_exists_Star p))
    [SMTPat (timeless (op_exists_Star p))]

val slprop_equiv (p q:slprop) : prop
val elim_slprop_equiv (#p #q:_) (_:slprop_equiv p q) : squash (p == q)
val slprop_post_equiv (#t:Type u#a) (p q: t -> slprop) : prop

val intro_slprop_post_equiv
       (#t:Type u#a)
       (p q: t -> slprop)
       (pf: (x:t -> slprop_equiv (p x) (q x)))
  : slprop_post_equiv p q

val elim_slprop_post_equiv (#t:Type u#a)
                          (p q: t -> slprop)
                          (pf:slprop_post_equiv p q)
                          (x:t)
    : slprop_equiv (p x) (q x)

val slprop_equiv_refl (v0:slprop) : slprop_equiv v0 v0

val slprop_equiv_sym (v0 v1:slprop) (_:slprop_equiv v0 v1)
  : slprop_equiv v1 v0

val slprop_equiv_trans (v0 v1 v2:slprop) (_:slprop_equiv v0 v1) (_:slprop_equiv v1 v2)
  : slprop_equiv v0 v2

val slprop_equiv_unit (x:slprop) : slprop_equiv (emp ** x) x

val slprop_equiv_comm (p1 p2:slprop)
  : slprop_equiv (p1 ** p2) (p2 ** p1)

val slprop_equiv_assoc (p1 p2 p3:slprop)
  : slprop_equiv ((p1 ** p2) ** p3) (p1 ** (p2 ** p3))

val slprop_equiv_exists (#a:Type) (p q : a -> slprop)
  (_ : squash (forall x. slprop_equiv (p x) (q x)))
  : slprop_equiv (op_exists_Star p) (op_exists_Star q)

val slprop_equiv_cong (p1 p2 p3 p4:slprop)
                     (_: slprop_equiv p1 p3)
                     (_: slprop_equiv p2 p4)
  : slprop_equiv (p1 ** p2) (p3 ** p4)

val slprop_equiv_ext (p1 p2:slprop) (_:p1 == p2)
  : slprop_equiv p1 p2


let star_assoc (p q r:slprop)
: Lemma (p ** (q ** r) == (p ** q) ** r)
= elim_slprop_equiv (slprop_equiv_assoc p q r)
let star_comm (p q:slprop)
: Lemma (p ** q == q ** p)
= elim_slprop_equiv (slprop_equiv_comm p q)
let emp_unit (p:slprop)
: Lemma (emp ** p == p)
= elim_slprop_equiv (slprop_equiv_unit p)
let slprop_equivs ()
: Lemma (
      (forall p q r. p ** (q ** r) == (p ** q) ** r) /\
      (forall p q. p ** q == q ** p) /\
      (forall p. emp ** p == p)
  )
= FStar.Classical.(
    forall_intro_3 star_assoc;
    forall_intro_2 star_comm;
    forall_intro emp_unit
  )

(***** end slprop_equiv *****)

////////////////////////////////////////////////////////////////////
// Invariants names and tokens
////////////////////////////////////////////////////////////////////
[@@ erasable]
val iname : Type0
// val storable_iname (i:iname) : GTot bool
val deq_iname : FStar.GhostSet.decide_eq iname
instance val non_informative_iname
  : NonInformative.non_informative iname

let inames = FStar.GhostSet.set iname
let fin_inames = is: inames { Pulse.Lib.GhostSet.is_finite is }
let emp_inames : inames = GhostSet.empty

let join_inames (is1 is2 : inames) : inames =
  GhostSet.union is1 is2

let inames_subset (is1 is2 : inames) : Type0 =
  GhostSet.subset is1 is2

let (/!) (is1 is2 : inames) : Type0 =
  GhostSet.disjoint is1 is2

val inv (i:iname) (p:slprop) : slprop

let mem_iname (e:inames) (i:iname) : erased bool = elift2 (fun e i -> GhostSet.mem i e) e i
let mem_inv (e:inames) (i:iname) : GTot bool = mem_iname e i

let single (i:iname) : inames = GhostSet.singleton deq_iname i
let add_inv (e:inames) (i:iname) : inames = GhostSet.union (single i) e
let remove_inv (e:inames) (i:iname) : inames = FStar.GhostSet.(intersect (complement (single i)) e)
let all_inames : inames = GhostSet.complement GhostSet.empty
let inv_disjointness_remove_i_i (e:inames) (i:iname)
  : Lemma (not (mem_inv (remove_inv e i) i)) = ()

(* Useful for reasoning about inames equalities. TODO: We need a decent
set of patterns. *)
val add_already_there (i:iname) (is:inames)
  : Lemma (requires GhostSet.mem i is)
          (ensures add_inv is i == is)
          [SMTPat (add_inv is i)]

(***** begin computation types and combinators *****)

////////////////////////////////////////////////////////////////////
// stt a pre post: The main type of a pulse computation
//  that when run in a state satisfying `pre`
//  may loop forever
//  but if it returns, it returns `x:a`
//  such that the final state satisfies `post x
////////////////////////////////////////////////////////////////////
[@@extract_as_impure_effect]
val stt (a:Type u#a) (pre:slprop) (post:a -> slprop) : Type0

val return_stt_noeq
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt a (p x) p

val bind_stt
  (#a:Type u#a) (#b:Type u#b)
  (#pre1:slprop) (#post1:a -> slprop) (#post2:b -> slprop)
  (e1:stt a pre1 post1)
  (e2:(x:a -> stt b (post1 x) post2))
: stt b pre1 post2

val frame_stt
  (#a:Type u#a)
  (#pre:slprop) (#post:a -> slprop)
  (frame:slprop)
  (e:stt a pre post)
: stt a (pre ** frame) (fun x -> post x ** frame)

val fork
  (#pre:slprop)
  (f:unit -> stt unit pre (fun _ -> emp))
: stt unit pre (fun _ -> emp)

val sub_stt (#a:Type u#a)
            (#pre1:slprop)
            (pre2:slprop)
            (#post1:a -> slprop)
            (post2:a -> slprop)
            (pf1 : slprop_equiv pre1 pre2)
            (pf2 : slprop_post_equiv post1 post2)
            (e:stt a pre1 post1)
: stt a pre2 post2

val conv_stt (#a:Type u#a)
            (#pre1:slprop)
            (#pre2:slprop)
            (#post1:a -> slprop)
            (#post2:a -> slprop)
            (pf1 : slprop_equiv pre1 pre2)
            (pf2 : slprop_post_equiv post1 post2)
: Lemma (stt a pre1 post1 == stt a pre2 post2)

val hide_div #a #pre #post (f:unit -> Dv (stt a pre post))
: stt a pre post

//////////////////////////////////////////////////////////////////////////
// Atomic computations, in three flavors
//////////////////////////////////////////////////////////////////////////

(* stt_atomic a #obs opens pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes a single concrete atomic step
   potentially opening invariants in `opens`
   and returns `x:a`
   such that the final state satisfies `post x`.

   The #obs index is used to indicate whether or not this computation has
   observable effects:

   - Observable:
     The computation has observable atomic effects on the physical state

   - Neutral:

     Has no observable effects and does not allocate or open invariants

   The indexes are ordered as follows, including in relation to the
   ghost effect:

   observable >...
                 |
                 v
       ghost > neutral > ghost non_info
*)
[@@extract_as_impure_effect]
val stt_atomic
    (a:Type u#a)
    (#[T.exact (`Observable)] obs:observability)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max 5 a)

val lift_observability
    (#a:Type u#a)
    (#obs #obs':_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
: stt_atomic a #(join_obs obs obs') opens pre post

val return_neutral
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt_atomic a #Neutral emp_inames (p x) (fun r -> p r ** pure (r == x))

val return_neutral_noeq
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt_atomic a #Neutral emp_inames (p x) p

val bind_atomic
    (#a:Type u#a)
    (#b:Type u#b)
    (#obs1:_)
    (#obs2:observability { at_most_one_observable obs1 obs2 })
    (#opens:inames)
    (#pre1:slprop)
    (#post1:a -> slprop)
    (#post2:b -> slprop)
    (e1:stt_atomic a #obs1 opens pre1 post1)
    (e2:(x:a -> stt_atomic b #obs2 opens (post1 x) post2))
: stt_atomic b #(join_obs obs1 obs2) opens pre1 post2

val frame_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop) (#post:a -> slprop)
    (frame:slprop)
    (e:stt_atomic a #obs opens pre post)
: stt_atomic a #obs opens (pre ** frame) (fun x -> post x ** frame)

val sub_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens:inames)
    (#pre1:slprop)
    (pre2:slprop)
    (#post1:a -> slprop)
    (post2:a -> slprop)
    (pf1 : slprop_equiv pre1 pre2)
    (pf2 : slprop_post_equiv post1 post2)
    (e:stt_atomic a #obs opens pre1 post1)
: stt_atomic a #obs opens pre2 post2

val sub_invs_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens1 #opens2:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens1 pre post)
    (_ : squash (inames_subset opens1 opens2))
: stt_atomic a #obs opens2 pre post

val lift_atomic
  (#a:Type u#a)
  (#obs:_)
  (#opens:inames)
  (#pre:slprop)
  (#post:a -> slprop)
  (e:stt_atomic a #obs opens pre post)
: stt a pre post

//////////////////////////////////////////////////////////////////////////
// Ghost computations
//////////////////////////////////////////////////////////////////////////

(* stt_ghost a opens pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes a single ghost step (i.e. a step that does not
   modify the heap, and does not get extracted)
   and returns `x:a`
   such that the final state satisfies `post x` *)
[@@ erasable]
val stt_ghost
    (a:Type u#a)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max 5 a)

val bind_ghost
    (#a:Type u#a)
    (#b:Type u#b)
    (#opens:inames)
    (#pre1:slprop)
    (#post1:a -> slprop)
    (#post2:b -> slprop)
    (e1:stt_ghost a opens pre1 post1)
    (e2:(x:a -> stt_ghost b opens (post1 x) post2))
: stt_ghost b opens pre1 post2

val lift_ghost_neutral
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_ghost a opens pre post)
    (ni_a:NonInformative.non_informative a)
: stt_atomic a #Neutral opens pre post

val lift_neutral_ghost
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #Neutral opens pre post)
: stt_ghost a opens pre post

val frame_ghost
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop) (#post:a -> slprop)
    (frame:slprop)
    (e:stt_ghost a opens pre post)
: stt_ghost a opens (pre ** frame) (fun x -> post x ** frame)

val sub_ghost
    (#a:Type u#a)
    (#opens:inames)
    (#pre1:slprop)
    (pre2:slprop)
    (#post1:a -> slprop)
    (post2:a -> slprop)
    (pf1 : slprop_equiv pre1 pre2)
    (pf2 : slprop_post_equiv post1 post2)
    (e:stt_ghost a opens pre1 post1)
: stt_ghost a opens pre2 post2

val sub_invs_ghost
    (#a:Type u#a)
    (#opens1 #opens2:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_ghost a opens1 pre post)
    (_ : squash (inames_subset opens1 opens2))
: stt_ghost a opens2 pre post

//////////////////////////////////////////////////////////////////////////
// Later
//////////////////////////////////////////////////////////////////////////

val later_credit (amt: nat) : slprop

val timeless_later_credit (amt: nat)
: Lemma (timeless (later_credit amt))
        [SMTPat (timeless (later_credit amt))]

val later_credit_zero ()
: Lemma (later_credit 0 == emp)

val later_credit_add (a b: nat)
: Lemma (later_credit (a + b) == later_credit a ** later_credit b)

inline_for_extraction [@@extract_as (`(fun (amt: nat) -> ()))]
val later_credit_buy (amt: nat)
: stt unit emp fun _ -> later_credit amt

val later (p: slprop) : slprop
val later_intro (p: slprop) : stt_ghost unit emp_inames p fun _ -> later p
val later_elim (p: slprop) : stt_ghost unit emp_inames (later p ** later_credit 1) fun _ -> p

val later_elim_timeless (p: slprop { timeless p }) : stt_ghost unit emp_inames (later p) (fun _ -> p)

val later_star p q : squash (later (p ** q) == later p ** later q)
val later_exists (#t: Type) (f:t->slprop) : stt_ghost unit emp_inames (later (exists* x. f x)) (fun _ -> exists* x. later (f x))
val exists_later (#t: Type) (f:t->slprop) : stt_ghost unit emp_inames (exists* x. later (f x)) (fun _ -> later (exists* x. f x))

//////////////////////////////////////////////////////////////////////////
// Equivalence
//////////////////////////////////////////////////////////////////////////

(* Two slprops are equal when approximated to the current heap level. *)
val equiv (a b: slprop) : slprop

val equiv_dup a b : stt_ghost unit emp_inames (equiv a b) fun _ -> equiv a b ** equiv a b
val equiv_refl a : stt_ghost unit emp_inames emp fun _ -> equiv a a
val equiv_comm a b : stt_ghost unit emp_inames (equiv a b) fun _ -> equiv b a
val equiv_trans a b c : stt_ghost unit emp_inames (equiv a b ** equiv b c) fun _ -> equiv a c

val equiv_elim a b : stt_ghost unit emp_inames (a ** equiv a b) fun _ -> b

val equiv_elim_timeless (a:slprop { timeless a }) (b: slprop { timeless b }) : stt_ghost unit emp_inames (equiv a b) fun _ -> pure (eq2 #slprop a b)

val equiv_star_congr (p q r: slprop) : squash (equiv q r == (equiv q r ** equiv (p ** q) (p ** r)))

val later_equiv (p q: slprop) : squash (later (equiv p q) == equiv (later p) (later q))

//////////////////////////////////////////////////////////////////////////
// Higher-order ghost state: references that can store predicates
//////////////////////////////////////////////////////////////////////////

[@@erasable]
val slprop_ref : Type0

val null_slprop_ref : slprop_ref

val slprop_ref_pts_to ([@@@mkey]x: slprop_ref) (y: slprop) : slprop

val slprop_ref_alloc (y: slprop)
: stt_ghost slprop_ref emp_inames emp fun x -> slprop_ref_pts_to x y

val slprop_ref_share (x: slprop_ref) (#y: slprop)
: stt_ghost unit emp_inames (slprop_ref_pts_to x y) fun _ -> slprop_ref_pts_to x y ** slprop_ref_pts_to x y

[@@allow_ambiguous]
val slprop_ref_gather (x: slprop_ref) (#y1 #y2: slprop)
: stt_ghost unit emp_inames (slprop_ref_pts_to x y1 ** slprop_ref_pts_to x y2) fun _ -> slprop_ref_pts_to x y1 ** later (equiv y1 y2)

//////////////////////////////////////////////////////////////////////////
// Invariants
//////////////////////////////////////////////////////////////////////////

val dup_inv (i:iname) (p:slprop)
  : stt_ghost unit emp_inames (inv i p) (fun _ -> inv i p ** inv i p)

val new_invariant (p:slprop)
: stt_ghost iname emp_inames p (fun i -> inv i p)

val fresh_invariant
    (ctx:inames { Pulse.Lib.GhostSet.is_finite ctx })
    (p:slprop)
: stt_ghost (i:iname { ~(i `GhostSet.mem` ctx) }) emp_inames p (fun i -> inv i p)

val with_invariant
    (#a:Type)
    (#obs:_)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:iname { not (mem_inv f_opens i) })
    ($f:unit -> stt_atomic a #obs f_opens
                           (later p ** fp)
                           (fun x -> later p ** fp' x))
: stt_atomic a #obs (add_inv f_opens i) (inv i p ** fp) (fun x -> inv i p ** fp' x)

val with_invariant_g
    (#a:Type)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:iname { not (mem_inv f_opens i) })
    ($f:unit -> stt_ghost a f_opens
                            (later p ** fp)
                            (fun x -> later p ** fp' x))
: stt_ghost a (add_inv f_opens i) (inv i p ** fp) (fun x -> inv i p ** fp' x)

[@@allow_ambiguous]
val invariant_name_identifies_invariant
      (#p #q:slprop)
      (i:iname)
      (j:iname { i == j } )
: stt_ghost
    unit
    emp_inames
    (inv i p ** inv j q)
    (fun _ -> inv i p ** inv j q ** later (equiv p q))

(***** end computation types and combinators *****)

(* This tactic is called to find non_informative witnesses.
It must run fast in the simple cases like unit and squash, but
also default to tcresolve before failing. *)
let non_info_tac () : T.Tac unit =
  Pulse.Lib.Tactics.non_info_tac ()

//////////////////////////////////////////////////////////////////////////
// Some basic actions and ghost operations
//////////////////////////////////////////////////////////////////////////

val rewrite (p:slprop) (q:slprop) (_:slprop_equiv p q)
: stt_ghost unit emp_inames p (fun _ -> q)

let rewrite_tactic_t = unit -> T.Tac unit

(* Useful for rewrites that are easier to prove by normalization/unification
than SMT. This tactic is also used by the checker when elaborating fold/unfold. *)
let slprop_equiv_norm (_:unit) : T.Tac unit =
    T.mapply (`slprop_equiv_refl)

(* TODO: Can these be made plugins? They would have to go into another module
   probably. *)

let slprop_equiv_unfold (head_sym:string) (_:unit) : T.Tac unit =
    T.mapply (`slprop_equiv_trans);
    T.norm [hnf; zeta; delta_only [head_sym]];
    T.norm [hnf; iota; primops];
    T.mapply (`slprop_equiv_refl);
    T.mapply (`slprop_equiv_refl)

let slprop_equiv_fold (head_sym:string) (_:unit) : T.Tac unit =
    T.mapply (`slprop_equiv_trans);
    T.flip();
    T.norm [hnf; zeta; delta_only [head_sym]];
    T.norm [hnf; iota; primops];
    T.mapply (`slprop_equiv_refl);
    T.mapply (`slprop_equiv_refl)
    
let slprop_equiv_ext' (p1 p2:slprop) (_: squash (p1 == p2))
  : slprop_equiv p1 p2 = slprop_equiv_refl p1

let match_rewrite_tac (_:unit) : T.Tac unit =
    let b = T.nth_var (-1) in
    T.norm []; // Needed, or otherwise the `tcut` in grewrite_eq can fail, unsure why.
    T.grewrite_eq b;
    T.mapply (`slprop_equiv_ext');
    T.trefl ()

let match_rename_tac (_:unit) : T.Tac unit =
    let open T in
    let b = T.nth_var (-1) in
    T.norm []; // Needed, or otherwise the `tcut` in grewrite_eq can fail, unsure why.
    try (
      T.grewrite_eq b;
      T.trefl ()
    )
    with _ -> T.smt()

[@@deprecated "Use (rewrite .. as .. by ..) syntax instead!"]
val rewrite_by (p:slprop) (q:slprop)
               (t:unit -> T.Tac unit)
               (_:unit { T.with_tactic t (slprop_equiv p q) })
: stt_ghost unit emp_inames p (fun _ -> q)

val elim_pure_explicit (p:prop)
: stt_ghost (squash p) emp_inames (pure p) (fun _ -> emp)

val elim_pure () (#p:prop)
: stt_ghost (squash p) emp_inames (pure p) (fun _ -> emp)

val intro_pure (p:prop) (_:squash p)
: stt_ghost unit emp_inames emp (fun _ -> pure p)

val elim_exists (#a:Type) (p:a -> slprop)
: stt_ghost (erased a) emp_inames (exists* x. p x) (fun x -> p (reveal x))

val intro_exists (#a:Type) (p:a -> slprop) (e:a)
: stt_ghost unit emp_inames (p e) (fun _ -> exists* x. p x)

val intro_exists_erased (#a:Type) (p:a -> slprop) (e:erased a)
: stt_ghost unit emp_inames (p (reveal e)) (fun _ -> exists* x. p x)

val stt_ghost_reveal (a:Type) (x:erased a)
: stt_ghost a emp_inames emp (fun y -> pure (reveal x == y))

val stt_admit (a:Type) (p:slprop) (q:a -> slprop)
: stt_atomic a #Neutral emp_inames p q

val assert_ (p:slprop)
: stt_ghost unit emp_inames p (fun _ -> p)

val assume_ (p:slprop)
: stt_ghost unit emp_inames emp (fun _ -> p)

val drop_ (p:slprop)
: stt_ghost unit emp_inames p (fun _ -> emp)

val unreachable (#a:Type) (#p:slprop) (#q:a -> slprop) (_:squash False)
: stt_ghost a emp_inames p q

val elim_false (a:Type) (p:a -> slprop)
: stt_ghost a emp_inames (pure False) p

// Finally, a big escape hatch for introducing architecture/backend-specific
// atomic operations from proven stt specifications
[@@warn_on_use "as_atomic is a an assumption"]
val as_atomic (#a:Type u#0) (pre:slprop) (post:a -> slprop)
              (pf:stt a pre post)
: stt_atomic a emp_inames pre post

(* Some syntactic sugar for iname sets. *)

(* An attribute to mark definitions to be unfolded
during checking `opens` annotations. We use to try
to make iname_list and @@ reduce away. *)
val unfold_check_opens : unit

[@@unfold_check_opens]
let (@@) : inames -> inames -> inames = join_inames

(* Attribute to eagerly unfold slprops in the context and goal. *)
val pulse_unfold : unit

val pulse_eager_unfold : unit

(*
`literally p` disables purification/extrusion preprocessing on `p`.

For example, `requires literally (exists* y. x |-> y)`
will compile to `stt .. (exists* y. x |-> y) ..`
instead of `#y: erased nat -> stt .. (x |-> y) ..`.

You can also use the `norewrite` keyword to disable preprocessing
for the whole function signature.
*)
unfold let literally (p: slprop) : slprop = p

(*
In a specification (i.e., after requires/ensures),
`old t` refers to the return value of `t`
where `t` is evaluated in the context of the precondition.
*)
let old () = ()

let rewrites_to_p #t (x y: t) = (x == y)

(*
`rewrites_to x t` instructs the Pulse matcher to globally replace `x` by `t` before matching.
(The first argument needs to be a variable.)

This is used in read functions to rewrite the return value
to the erased value, which makes nested dereferencing (!(!x)) work.

fn ( ! ) #t (x: ref t) (y: erased t)
  preserves x |-> y
  returns result: t
  ensures rewrites_to result y
*)
[@@pulse_unfold] let rewrites_to #t (x y: t) = pure (rewrites_to_p x y)

[@@coercion; pulse_unfold; strict_on_arguments [0]; unfold_check_opens]
let rec iname_list (xs : list iname) : inames =
  match xs with
  | [] -> emp_inames
  | i::is -> add_inv (iname_list is) i
