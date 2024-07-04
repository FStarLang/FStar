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
module G = FStar.Ghost
module Set = FStar.Set
module T = FStar.Tactics.V2

(* This attribute can be used on the indexes of a slprop
   to instruct the checker to call the SMT solver to relate
   occurrences of that index.

   For example, if you have

     val pts_to (x:ref a) ([@@@equate_by_smt] v:a) : slprop

   Then `pts_to x (a + b)` and `pts_to x (b + a)` will be
   matched by the prover by emitting an SMT query (a + b) == (b + a). Of course, 
   `pts_to x a` and `pts_to x a` will be matched purely by unification without
   emitted a trivial SMT query (a == a).

   By default, if none of the indexes of a slprop are marked with "equate_by_smt", 
   the _last_ argument of a slprop is considered to be equated by SMT. This makes 
   it convenient to write slprops like the one below, without paying special
   heed to this attribute.
  
     val pts_to (x:ref a) (v:a) : slprop
*)
val equate_by_smt    : unit (* now meaningless. *)
val equate_strict    : unit (* only use fastunif *)
val equate_syntactic : unit (* only use term_eq *)

(** This attribute allows to do ambiguous proving when calling a function. *)
val allow_ambiguous : unit

(***** begin slprop_equiv *****)

[@@erasable]
val slprop : Type u#4

[@@erasable]
val slprop2_base : Type u#3
val down2 (p:slprop) : slprop2_base
val up2 (p:slprop2_base) : slprop
let is_slprop2 (v:slprop) : prop = up2 (down2 v) == v
val up2_is_slprop2 (p:slprop2_base) : Lemma (is_slprop2 (up2 p))

[@@erasable]
val slprop1_base : Type u#2
val down1 (p:slprop) : slprop1_base
val up1 (p:slprop1_base) : slprop
let is_slprop1 (v:slprop) : prop = up1 (down1 v) == v
val up1_is_slprop1 (p:slprop1_base) : Lemma (is_slprop1 (up1 p))

let slprop2 = s:slprop { is_slprop2 s }
let slprop1 = s:slprop { is_slprop1 s }

(* Storable slprops: a storable0 (or storable) can be stored in the heap
(made into an invariant), and obtain an slprop asserting this fact.
A storable1, can be stored "twice", in the sense that it can be stored
in the heap, obtain a pts_to for it, and that pts_to can in turn be stored
as an invariant.

As the heap stack is extended, these names retain their meaning as being
"N+1" away from the top of the stack. *)

let storable0    = slprop2
let is_storable0 = is_slprop2
let storable1    = slprop1
let is_storable1 = is_slprop1

let storable    = storable0
let is_storable = is_storable0


//
// A note on smt patterns on is_slprop1 and is_slprop2 lemmas:
//
// While the patterns on the individual lemmas are goal-directed,
//   there are multiple ways to prove, say, is_slprop2 (p ** q)
//
// Either via, is_slprop2 p /\ is_slprop2 q ==> is_slprop2 (p ** q)
// or via, is_slprop1 p /\ is_slprop1 q ==> is_slprop1 (p ** q) ==> is_slprop2 (p ** q)
//
// This is a bit suboptimal
//
val slprop_1_is_2 (v:slprop)
  : Lemma (is_slprop1 v ==> is_slprop2 v)
          [SMTPat (is_slprop2 v)]

val emp : slprop
val emp_is_slprop1 : squash (is_slprop1 emp)

val pure (p:prop) : slprop
val pure_is_slprop1 (p:prop)
  : Lemma (is_slprop1 (pure p))
          [SMTPat (is_slprop1 (pure p))]

val ( ** ) (p q:slprop) : slprop

val slprop2_star (p q : slprop)
: Lemma
    (requires is_slprop2 p /\ is_slprop2 q)
    (ensures is_slprop2 (p ** q))
    [SMTPat (is_slprop2 (p ** q))]

val slprop1_star (p q : slprop)
: Lemma
    (requires is_slprop1 p /\ is_slprop1 q)
    (ensures is_slprop1 (p ** q))
    [SMTPat (is_slprop1 (p ** q))]

val ( exists* ) (#a:Type) (p:a -> slprop) : slprop

val slprop2_exists (#a:Type u#a) (p: a -> slprop)
: Lemma
    (requires forall x. is_slprop2 (p x))
    (ensures is_slprop2 (op_exists_Star p))
    [SMTPat (is_slprop2 (op_exists_Star p))]

val slprop1_exists (#a:Type u#a) (p: a -> slprop)
: Lemma
    (requires forall x. is_slprop1 (p x))
    (ensures is_slprop1 (op_exists_Star p))
    [SMTPat (is_slprop1 (op_exists_Star p))]

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
  : slprop_equiv (p1 ** p2 ** p3) (p1 ** (p2 ** p3))

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
val deq_iname : FStar.GhostSet.decide_eq iname
instance val non_informative_iname
  : NonInformative.non_informative iname

let inames = FStar.GhostSet.set iname
let emp_inames : inames = GhostSet.empty

let join_inames (is1 is2 : inames) : inames =
  GhostSet.union is1 is2

let inames_subset (is1 is2 : inames) : Type0 =
  GhostSet.subset is1 is2

let (/!) (is1 is2 : inames) : Type0 =
  GhostSet.disjoint is1 is2

val inv (i:iname) (p:vprop) : vprop

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

val par_stt
  (#preL:slprop)
  (#postL:slprop) 
  (#preR:slprop)
  (#postR:slprop)
  (f:stt unit preL (fun _ -> postL))
  (g:stt unit preR (fun _ -> postR))
: stt unit
      (preL ** preR)
      (fun _ -> postL ** postR)

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
: Type u#(max 4 a)

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

val lift_atomic0
  (#a:Type u#0)
  (#obs:_)
  (#opens:inames)
  (#pre:slprop)
  (#post:a -> slprop)
  (e:stt_atomic a #obs opens pre post)
: stt a pre post

val lift_atomic1
  (#a:Type u#1)
  (#obs:_)
  (#opens:inames)
  (#pre:slprop)
  (#post:a -> slprop)
  (e:stt_atomic a #obs opens pre post)
: stt a pre post

val lift_atomic2
  (#a:Type u#2)
  (#obs:_)
  (#opens:inames)
  (#pre:slprop)
  (#post:a -> slprop)
  (e:stt_atomic a #obs opens pre post)
: stt a pre post

val lift_atomic3
  (#a:Type u#3)
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
: Type u#(max 4 a)

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
// Invariants
//////////////////////////////////////////////////////////////////////////

val dup_inv (i:iname) (p:slprop)
  : stt_ghost unit emp_inames (inv i p) (fun _ -> inv i p ** inv i p)

val new_invariant (p:storable)
: stt_ghost iname emp_inames p (fun i -> inv i p)

val fresh_wrt (i:iname) (c:list iname)
: prop

val fresh_wrt_def (i:iname) (c:list iname)
: Lemma
    (fresh_wrt i c <==>
    (forall i'. List.Tot.memP i' c ==> i' =!= i))
    [SMTPat (fresh_wrt i c)]

val fresh_invariant
    (ctx:list iname)
    (p:storable)
: stt_ghost (i:iname { i `fresh_wrt` ctx }) emp_inames p (fun i -> inv i p)

val with_invariant
    (#a:Type)
    (#obs:_)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:iname { not (mem_inv f_opens i) })
    ($f:unit -> stt_atomic a #obs f_opens
                           (p ** fp)
                           (fun x -> p ** fp' x))
: stt_atomic a #obs (add_inv f_opens i) (inv i p ** fp) (fun x -> inv i p ** fp' x)

val with_invariant_g
    (#a:Type)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:iname { not (mem_inv f_opens i) })
    ($f:unit -> stt_ghost a f_opens
                            (p ** fp)
                            (fun x -> p ** fp' x))
: stt_ghost a (add_inv f_opens i) (inv i p ** fp) (fun x -> inv i p ** fp' x)

val distinct_invariants_have_distinct_names
    (#p #q:slprop)
    (i j:iname)
    (_:squash (p =!= q))
: stt_ghost
    (_:squash (i =!= j))
    emp_inames
    (inv i p ** inv j q)
    (fun _ -> inv i p ** inv j q)

[@@allow_ambiguous]
val invariant_name_identifies_invariant
      (#p #q:slprop)
      (i:iname)
      (j:iname { i == j } )
: stt_ghost
    (squash (p == q))
    emp_inames
    (inv i p ** inv j q)
    (fun _ -> inv i p ** inv j q)

(***** end computation types and combinators *****)

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

////////////////////////////////////////////////////////
//Core PCM references
////////////////////////////////////////////////////////
val core_pcm_ref : Type0
val null_core_pcm_ref : core_pcm_ref
val is_null_core_pcm_ref (p:core_pcm_ref)
  : b:bool { b <==> p == null_core_pcm_ref }

let pcm_ref
    (#a:Type u#a)
    (p:FStar.PCM.pcm a)
: Type0
= core_pcm_ref

val pcm_pts_to
    (#a:Type u#1)
    (#p:pcm a)
    ([@@@equate_strict] r:pcm_ref p)
    (v:a)
: slprop

val is_slprop1_pcm_pts_to
    (#a:Type u#1)
    (#p:pcm a)
    (r:pcm_ref p)
    (v:a)
: Lemma (is_slprop1 (pcm_pts_to r v))
        [SMTPat (is_slprop1 (pcm_pts_to r v))]

let pcm_ref_null
    (#a:Type)
    (p:FStar.PCM.pcm a)
: pcm_ref p
= null_core_pcm_ref

let is_pcm_ref_null
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:pcm_ref p)
: b:bool { b <==> r == pcm_ref_null p }
= is_null_core_pcm_ref r

val pts_to_not_null
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:pcm_ref p)
    (v:a)
: stt_ghost (squash (not (is_pcm_ref_null r)))
            emp_inames
            (pcm_pts_to r v)
            (fun _ -> pcm_pts_to r v)

val alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: stt (pcm_ref pcm)
      emp
      (fun r -> pcm_pts_to r x)

val read
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt (v:a{compatible p x v /\ p.refine v})
     (pcm_pts_to r x)
     (fun v -> pcm_pts_to r (f v))

val write
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt unit
     (pcm_pts_to r x)
     (fun _ -> pcm_pts_to r y)

val share
    (#a:Type)
    (#pcm:pcm a)
    (r:pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (pcm_pts_to r (v0 `op pcm` v1))
    (fun _ -> pcm_pts_to r v0 ** pcm_pts_to r v1)

[@@allow_ambiguous]
val gather
    (#a:Type)
    (#pcm:pcm a)
    (r:pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (pcm_pts_to r v0 ** pcm_pts_to r v1)
    (fun _ -> pcm_pts_to r (op pcm v0 v1))

/////////////////////////////////////////////////////////////////////////
[@@erasable]
val core_ghost_pcm_ref : Type0

let ghost_pcm_ref
    (#a:Type u#a)
    (p:FStar.PCM.pcm a)
: Type0
= core_ghost_pcm_ref

instance val non_informative_ghost_pcm_ref
  (a:Type u#a) (p:FStar.PCM.pcm a)
  : NonInformative.non_informative (ghost_pcm_ref p)

val ghost_pcm_pts_to
    (#a:Type u#1)
    (#p:pcm a)
    ([@@@equate_strict] r:ghost_pcm_ref p)
    (v:a)
: slprop

val is_slprop1_ghost_pcm_pts_to
    (#a:Type u#1)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (v:a)
: Lemma (is_slprop1 (ghost_pcm_pts_to r v))
        [SMTPat (is_slprop1 (ghost_pcm_pts_to r v))]

val ghost_alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: stt_ghost (ghost_pcm_ref pcm)
    emp_inames
    emp
    (fun r -> ghost_pcm_pts_to r x)

val ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt_ghost (erased (v:a{compatible p x v /\ p.refine v}))
    emp_inames
    (ghost_pcm_pts_to r x)
    (fun v -> ghost_pcm_pts_to r (f v))

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_ghost unit
    emp_inames
    (ghost_pcm_pts_to r x)
    (fun _ -> ghost_pcm_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (ghost_pcm_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pcm_pts_to r v0 ** ghost_pcm_pts_to r v1)

[@@allow_ambiguous]
val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (ghost_pcm_pts_to r v0 ** ghost_pcm_pts_to r v1)
    (fun _ -> ghost_pcm_pts_to r (op pcm v0 v1))

////////////////////////////////////////////////////////
//Big PCM references
////////////////////////////////////////////////////////
val big_pcm_pts_to
    (#a:Type u#2)
    (#p:pcm a)
    ([@@@equate_strict] r:pcm_ref p)
    (v:a)
: slprop


val is_slprop2_big_pcm_pts_to
    (#a:Type u#2)
    (#p:pcm a)
    (r:pcm_ref p)
    (v:a)
: Lemma (is_slprop2 (big_pcm_pts_to r v))
        [SMTPat (is_slprop2 (big_pcm_pts_to r v))]

val big_pts_to_not_null
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:pcm_ref p)
    (v:a)
: stt_ghost (squash (not (is_pcm_ref_null r)))
            emp_inames
            (big_pcm_pts_to r v)
            (fun _ -> big_pcm_pts_to r v)

val big_alloc
    (#a:Type u#2)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: stt (pcm_ref pcm)
    emp
    (fun r -> big_pcm_pts_to r x)

val big_read
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt (v:a{compatible p x v /\ p.refine v})
    (big_pcm_pts_to r x)
    (fun v -> big_pcm_pts_to r (f v))

val big_write
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt unit
    (big_pcm_pts_to r x)
    (fun _ -> big_pcm_pts_to r y)

val big_share
    (#a:Type)
    (#pcm:pcm a)
    (r:pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (big_pcm_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_pcm_pts_to r v0 ** big_pcm_pts_to r v1)

[@@allow_ambiguous]
val big_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (big_pcm_pts_to r v0 ** big_pcm_pts_to r v1)
    (fun _ -> big_pcm_pts_to r (op pcm v0 v1))

val big_ghost_pcm_pts_to
    (#a:Type u#2)
    (#p:pcm a)
    ([@@@equate_strict] r:ghost_pcm_ref p)
    (v:a)
: slprop

val is_slprop2_big_ghost_pcm_pts_to
    (#a:Type u#2)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (v:a)
: Lemma (is_slprop2 (big_ghost_pcm_pts_to r v))
        [SMTPat (is_slprop2 (big_ghost_pcm_pts_to r v))]

val big_ghost_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: stt_ghost (ghost_pcm_ref pcm)
    emp_inames
    emp
    (fun r -> big_ghost_pcm_pts_to r x)

val big_ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt_ghost (erased (v:a{compatible p x v /\ p.refine v}))
    emp_inames
    (big_ghost_pcm_pts_to r x)
    (fun v -> big_ghost_pcm_pts_to r (f v))

val big_ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_ghost unit
    emp_inames
    (big_ghost_pcm_pts_to r x)
    (fun _ -> big_ghost_pcm_pts_to r y)

val big_ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (big_ghost_pcm_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_ghost_pcm_pts_to r v0 ** big_ghost_pcm_pts_to r v1)

[@@allow_ambiguous]
val big_ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (big_ghost_pcm_pts_to r v0 ** big_ghost_pcm_pts_to r v1)
    (fun _ -> big_ghost_pcm_pts_to r (op pcm v0 v1))

////////////////////////////////////////////////////////
//Non-boxable PCM references
////////////////////////////////////////////////////////
val nb_pcm_pts_to
    (#a:Type u#3)
    (#p:pcm a)
    (r:pcm_ref p)
    (v:a)
: slprop

val nb_pts_to_not_null
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:pcm_ref p)
    (v:a)
: stt_ghost (squash (not (is_pcm_ref_null r)))
            emp_inames
            (nb_pcm_pts_to r v)
            (fun _ -> nb_pcm_pts_to r v)

val nb_alloc
    (#a:Type u#3)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: stt (pcm_ref pcm)
    emp
    (fun r -> nb_pcm_pts_to r x)

val nb_read
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt (v:a{compatible p x v /\ p.refine v})
    (nb_pcm_pts_to r x)
    (fun v -> nb_pcm_pts_to r (f v))

val nb_write
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt unit
    (nb_pcm_pts_to r x)
    (fun _ -> nb_pcm_pts_to r y)

val nb_share
    (#a:Type)
    (#pcm:pcm a)
    (r:pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (nb_pcm_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_pcm_pts_to r v0 ** nb_pcm_pts_to r v1)

val nb_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (nb_pcm_pts_to r v0 ** nb_pcm_pts_to r v1)
    (fun _ -> nb_pcm_pts_to r (op pcm v0 v1))

val nb_ghost_pcm_pts_to
    (#a:Type u#3)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (v:a)
: slprop


val nb_ghost_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: stt_ghost (ghost_pcm_ref pcm)
    emp_inames
    emp
    (fun r -> nb_ghost_pcm_pts_to r x)

val nb_ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt_ghost (erased (v:a{compatible p x v /\ p.refine v}))
    emp_inames
    (nb_ghost_pcm_pts_to r x)
    (fun v -> nb_ghost_pcm_pts_to r (f v))

val nb_ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_ghost unit
    emp_inames
    (nb_ghost_pcm_pts_to r x)
    (fun _ -> nb_ghost_pcm_pts_to r y)

val nb_ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (nb_ghost_pcm_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_ghost_pcm_pts_to r v0 ** nb_ghost_pcm_pts_to r v1)

val nb_ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (nb_ghost_pcm_pts_to r v0 ** nb_ghost_pcm_pts_to r v1)
    (fun _ -> nb_ghost_pcm_pts_to r (op pcm v0 v1))


// Finally, a big escape hatch for introducing architecture/backend-specific
// atomic operations from proven stt specifications
[@@warn_on_use "as_atomic is a an assumption"]
val as_atomic (#a:Type u#0) (pre:slprop) (post:a -> slprop)
              (pf:stt a pre post)
: stt_atomic a emp_inames pre post
