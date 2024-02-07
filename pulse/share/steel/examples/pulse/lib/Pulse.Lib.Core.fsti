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
module U32 = FStar.UInt32
module G = FStar.Ghost
module Set = FStar.Set
module T = FStar.Tactics.V2
(* Common alias *)
let one_half =
  half_perm full_perm

val double_one_half ()
  : Lemma (sum_perm one_half one_half == full_perm)

(* This attribute can be used on the indexes of a vprop
   to instruct the checker to call the SMT solver to relate
   occurrences of that index.

   For example, if you have

     val pts_to (x:ref a) ([@@@equate_by_smt] v:a) : vprop

   Then `pts_to x (a + b)` and `pts_to x (b + a)` will be
   matched by the prover by emitting an SMT query (a + b) == (b + a). Of course, 
   `pts_to x a` and `pts_to x a` will be matched purely by unification without
   emitted a trivial SMT query (a == a).

   By default, if none of the indexes of a vprop are marked with "equate_by_smt", 
   the _last_ argument of a vprop is considered to be equated by SMT. This makes 
   it convenient to write vprops like the one below, without paying special
   heed to this attribute.
  
     val pts_to (x:ref a) (v:a) : vprop
*)
val equate_by_smt : unit
(***** begin vprop_equiv *****)

#set-options "--print_implicits --ugly --print_universes"

[@@erasable]
val vprop : Type u#2

val emp : vprop
val ( ** ) (p q:vprop) : vprop
val pure (p:prop) : vprop
val ( exists* ) (#a:Type) (p:a -> vprop) : vprop
val vprop_equiv (p q:vprop) : prop
val elim_vprop_equiv (#p #q:_) (_:vprop_equiv p q) : squash (p == q)
val vprop_post_equiv (#t:Type u#a) (p q: t -> vprop) : prop

val intro_vprop_post_equiv
       (#t:Type u#a) 
       (p q: t -> vprop)
       (pf: (x:t -> vprop_equiv (p x) (q x)))
  : vprop_post_equiv p q

val elim_vprop_post_equiv (#t:Type u#a)
                          (p q: t -> vprop) 
                          (pf:vprop_post_equiv p q)
                          (x:t) 
    : vprop_equiv (p x) (q x)

val vprop_equiv_refl (v0:vprop) : vprop_equiv v0 v0

val vprop_equiv_sym (v0 v1:vprop) (_:vprop_equiv v0 v1)
  : vprop_equiv v1 v0

val vprop_equiv_trans (v0 v1 v2:vprop) (_:vprop_equiv v0 v1) (_:vprop_equiv v1 v2)
  : vprop_equiv v0 v2

val vprop_equiv_unit (x:vprop) : vprop_equiv (emp ** x) x

val vprop_equiv_comm (p1 p2:vprop)
  : vprop_equiv (p1 ** p2) (p2 ** p1)

val vprop_equiv_assoc (p1 p2 p3:vprop)
  : vprop_equiv (p1 ** p2 ** p3) (p1 ** (p2 ** p3))

val vprop_equiv_cong (p1 p2 p3 p4:vprop)
                     (_: vprop_equiv p1 p3)
                     (_: vprop_equiv p2 p4)
  : vprop_equiv (p1 ** p2) (p3 ** p4)

val vprop_equiv_ext (p1 p2:vprop) (_:p1 == p2)
  : vprop_equiv p1 p2

(***** end vprop_equiv *****)

////////////////////////////////////////////////////////////////////
// Invariants names and tokens
////////////////////////////////////////////////////////////////////
val iname : eqtype
let inames = erased (FStar.Set.set iname)
let emp_inames : inames = Ghost.hide Set.empty

let join_inames (is1 is2 : inames) : inames =
  Set.union is1 is2

let inames_subset (is1 is2 : inames) : Type0 =
  Set.subset is1 is2

let (/!) (is1 is2 : inames) : Type0 =
  Set.disjoint is1 is2

val inv (p:vprop) : Type u#0

val name_of_inv #p (i : inv p) : GTot iname

let mem_iname (e:inames) (i:iname) : erased bool = elift2 (fun e i -> Set.mem i e) e i
let mem_inv (#p:vprop) (e:inames) (i:inv p) : erased bool = mem_iname e (name_of_inv i)

let add_iname (e:inames) (i:iname) : inames = Set.union (Set.singleton i) (reveal e)
let add_inv (#p:vprop) (e:inames) (i:inv p) : inames = add_iname e (name_of_inv i)
let remove_inv (#p:vprop) (e:inames) (i:inv p) : inames = Set.remove (name_of_inv i) e
let all_inames : inames = Set.complement Set.empty
let inv_disjointness_remove_i_i (#p:vprop) (e:inames) (i:inv p)
: Lemma (not (mem_inv (remove_inv e i) i))
= ()
(* Useful for reasoning about inames equalities. TODO: We need a decent
set of patterns. *)
val add_already_there #p (i : inv p) (is : inames)
  : Lemma (requires Set.mem (name_of_inv i) is)
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
val stt (a:Type u#a) (pre:vprop) (post:a -> vprop) : Type0

val return_stt_noeq
    (#a:Type u#a)
    (x:a)
    (p:a -> vprop)
: stt a (p x) p

val bind_stt
  (#a:Type u#a) (#b:Type u#b)
  (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt a pre1 post1)
  (e2:(x:a -> stt b (post1 x) post2))
: stt b pre1 post2

val frame_stt
  (#a:Type u#a)
  (#pre:vprop) (#post:a -> vprop)
  (frame:vprop)
  (e:stt a pre post)
: stt a (pre ** frame) (fun x -> post x ** frame)

val par_stt
  (#preL:vprop)
  (#postL:vprop) 
  (#preR:vprop)
  (#postR:vprop)
  (f:stt unit preL (fun _ -> postL))
  (g:stt unit preR (fun _ -> postR))
: stt unit
      (preL ** preR)
      (fun _ -> postL ** postR)

val sub_stt (#a:Type u#a)
            (#pre1:vprop)
            (pre2:vprop)
            (#post1:a -> vprop)
            (post2:a -> vprop)
            (pf1 : vprop_equiv pre1 pre2)
            (pf2 : vprop_post_equiv post1 post2)
            (e:stt a pre1 post1)
: stt a pre2 post2

val conv_stt (#a:Type u#a)
            (#pre1:vprop)
            (#pre2:vprop)
            (#post1:a -> vprop)
            (#post2:a -> vprop)
            (pf1 : vprop_equiv pre1 pre2)
            (pf2 : vprop_post_equiv post1 post2)
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

   - Unobservable:
     
     Has no observable effects, but may allocate or open invariants---will
     be erased by the compiler if the result type is also non-informative

   - Neutral:

     Has no observable effects and does not allocate or open invariants

   The indexes are ordered as follows, including in relation to the
   ghost effect:

   observable > unobservable
                 |
                 v
       ghost > neutral > ghost non_info
*)
[@@extract_as_impure_effect]
val stt_atomic
    (a:Type u#a)
    (#[T.exact (`Observable)] obs:observability)
    (opens:inames)
    (pre:vprop)
    (post:a -> vprop)
: Type u#(max 2 a)

val lift_observability
    (#a:Type u#a)
    (#obs #obs':_)
    (#opens:inames)
    (#pre:vprop)
    (#post:a -> vprop)
    (e:stt_atomic a #obs opens pre post)
: stt_atomic a #(join_obs obs obs') opens pre post

val return_neutral
    (#a:Type u#a)
    (x:a)
    (p:a -> vprop)
: stt_atomic a #Neutral emp_inames (p x) (fun r -> p r ** pure (r == x))

val return_neutral_noeq
    (#a:Type u#a)
    (x:a)
    (p:a -> vprop)
: stt_atomic a #Neutral emp_inames (p x) p

val bind_atomic
    (#a:Type u#a)
    (#b:Type u#b)
    (#obs1:_)
    (#obs2:observability { at_most_one_observable obs1 obs2 })
    (#opens:inames)
    (#pre1:vprop)
    (#post1:a -> vprop)
    (#post2:b -> vprop)
    (e1:stt_atomic a #obs1 opens pre1 post1)
    (e2:(x:a -> stt_atomic b #obs2 opens (post1 x) post2))
: stt_atomic b #(join_obs obs1 obs2) opens pre1 post2

val frame_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens:inames)
    (#pre:vprop) (#post:a -> vprop)
    (frame:vprop)
    (e:stt_atomic a #obs opens pre post)
: stt_atomic a #obs opens (pre ** frame) (fun x -> post x ** frame)

val sub_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens:inames)
    (#pre1:vprop)
    (pre2:vprop)
    (#post1:a -> vprop)
    (post2:a -> vprop)
    (pf1 : vprop_equiv pre1 pre2)
    (pf2 : vprop_post_equiv post1 post2)
    (e:stt_atomic a #obs opens pre1 post1)
: stt_atomic a #obs opens pre2 post2

val sub_invs_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens1 #opens2:inames)
    (#pre:vprop)
    (#post:a -> vprop)
    (e:stt_atomic a #obs opens1 pre post)
    (_ : squash (inames_subset opens1 opens2))
: stt_atomic a #obs opens2 pre post

val lift_atomic0
(#a:Type u#0)
  (#obs:_)
  (#opens:inames)
  (#pre:vprop)
  (#post:a -> vprop)
  (e:stt_atomic a #obs opens pre post)
: stt a pre post

val lift_atomic1
  (#a:Type u#1)
  (#obs:_)
  (#opens:inames)
  (#pre:vprop)
  (#post:a -> vprop)
  (e:stt_atomic a #obs opens pre post)
: stt a pre post

val lift_atomic2
  (#a:Type u#2)
  (#obs:_)
  (#opens:inames)
  (#pre:vprop)
  (#post:a -> vprop)
  (e:stt_atomic a #obs opens pre post)
: stt a pre post

val new_invariant
    (p:vprop)
: stt_atomic (inv p) #Unobservable emp_inames p (fun _ -> emp)

val with_invariant
    (#a:Type)
    (#obs:_)
    (#fp:vprop)
    (#fp':a -> vprop)
    (#f_opens:inames)
    (#p:vprop)
    (i:inv p{not (mem_inv f_opens i)})
    ($f:unit -> stt_atomic a #obs f_opens
                            (p ** fp)
                            (fun x -> p ** fp' x))
: stt_atomic a #(join_obs obs Unobservable) (add_inv f_opens i) fp fp'

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
    (pre:vprop)
    (post:a -> vprop)
: Type u#(max 2 a)

val bind_ghost
    (#a:Type u#a)
    (#b:Type u#b)
    (#pre1:vprop)
    (#post1:a -> vprop)
    (#post2:b -> vprop)
    (e1:stt_ghost a pre1 post1)
    (e2:(x:a -> stt_ghost b (post1 x) post2))
: stt_ghost b pre1 post2

type non_informative_witness (a:Type u#a) =
  x:Ghost.erased a -> y:a{y == Ghost.reveal x}

val lift_ghost_neutral
    (#a:Type u#a)
    (#pre:vprop)
    (#post:a -> vprop)
    (e:stt_ghost a pre post)
    (reveal_a:non_informative_witness a)
: stt_atomic a #Neutral emp_inames pre post

val lift_neutral_ghost
    (#a:Type u#a)
    (#pre:vprop)
    (#post:a -> vprop)
    (e:stt_atomic a #Neutral emp_inames pre post)
: stt_ghost a pre post

val frame_ghost
    (#a:Type u#a)
    (#pre:vprop) (#post:a -> vprop)
    (frame:vprop)
    (e:stt_ghost a pre post)
: stt_ghost a (pre ** frame) (fun x -> post x ** frame)

val sub_ghost
    (#a:Type u#a)
    (#pre1:vprop)
    (pre2:vprop)
    (#post1:a -> vprop)
    (post2:a -> vprop)
    (pf1 : vprop_equiv pre1 pre2)
    (pf2 : vprop_post_equiv post1 post2)
    (e:stt_ghost a pre1 post1)
: stt_ghost a pre2 post2

inline_for_extraction
let unit_non_informative
: non_informative_witness unit
= fun u -> u

inline_for_extraction
let prop_non_informative
: non_informative_witness prop
= fun p -> p

inline_for_extraction
let erased_non_informative (a:Type u#a)
: non_informative_witness (Ghost.erased u#a a)
= fun x -> Ghost.reveal x

inline_for_extraction
let squash_non_informative (a:Type u#a)
: non_informative_witness (squash  u#a a)
= fun x -> x

(***** end computation types and combinators *****)

//////////////////////////////////////////////////////////////////////////
// Some basic actions and ghost operations
//////////////////////////////////////////////////////////////////////////

val rewrite (p:vprop) (q:vprop) (_:vprop_equiv p q)
: stt_ghost unit p (fun _ -> q)

val rewrite_by (p:vprop) (q:vprop) 
               (t:unit -> T.Tac unit)
               (_:unit { T.with_tactic t (vprop_equiv p q) })
: stt_ghost unit p (fun _ -> q)

val elim_pure_explicit (p:prop)
: stt_ghost (squash p) (pure p) (fun _ -> emp)

val elim_pure () (#p:prop)
: stt_ghost (squash p) (pure p) (fun _ -> emp)

val intro_pure (p:prop) (_:squash p)
: stt_ghost unit emp (fun _ -> pure p)

val elim_exists (#a:Type) (p:a -> vprop)
: stt_ghost (erased a) (exists* x. p x) (fun x -> p (reveal x))

val intro_exists (#a:Type) (p:a -> vprop) (e:a)
: stt_ghost unit (p e) (fun _ -> exists* x. p x)

val intro_exists_erased (#a:Type) (p:a -> vprop) (e:erased a)
: stt_ghost unit (p (reveal e)) (fun _ -> exists* x. p x)

val stt_ghost_reveal (a:Type) (x:erased a)
: stt_ghost a emp (fun y -> pure (reveal x == y))

val stt_admit (a:Type) (p:vprop) (q:a -> vprop)
: stt_atomic a #Neutral emp_inames p q

val assert_ (p:vprop)
: stt_ghost unit p (fun _ -> p)

val assume_ (p:vprop)
: stt_ghost unit emp (fun _ -> p)

val drop_ (p:vprop)
: stt_ghost unit p (fun _ -> emp)

val unreachable (#a:Type) (#p:vprop) (#q:a -> vprop) (_:squash False)
: stt_ghost a p q

val elim_false (a:Type) (p:a -> vprop)
: stt_ghost a (pure False) p

////////////////////////////////////////////////////////
//Core PCM references
////////////////////////////////////////////////////////
val pcm_ref
    (#[@@@unused] a:Type u#a)
    ([@@@unused] p:FStar.PCM.pcm a)
: Type0

val pcm_pts_to
    (#a:Type u#1)
    (#p:pcm a)
    (r:pcm_ref p)
    (v:a)
: vprop

val pcm_ref_null
    (#a:Type)
    (p:FStar.PCM.pcm a)
: pcm_ref p

val is_pcm_ref_null
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:pcm_ref p)
: b:bool { b <==> r == pcm_ref_null p }

val pts_to_not_null
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:pcm_ref p)
    (v:a)
: stt_ghost (squash (not (is_pcm_ref_null r)))
            (pcm_pts_to r v)
            (fun _ -> pcm_pts_to r v)

val alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:a{compatible pcm x x /\ pcm.refine x})
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
    (pcm_pts_to r (v0 `op pcm` v1))
    (fun _ -> pcm_pts_to r v0 ** pcm_pts_to r v1)

val gather
    (#a:Type)
    (#pcm:pcm a)
    (r:pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    (pcm_pts_to r v0 ** pcm_pts_to r v1)
    (fun _ -> pcm_pts_to r (op pcm v0 v1))

/////////////////////////////////////////////////////////////////////////

[@@erasable]
val ghost_pcm_ref
    (#[@@@unused] a:Type u#a)
    ([@@@unused] p:FStar.PCM.pcm a)
: Type0

val ghost_pcm_pts_to
    (#a:Type u#1)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (v:a)
: vprop

val ghost_alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:erased a{compatible pcm x x /\ pcm.refine x})
: stt_ghost (ghost_pcm_ref pcm)
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
    (ghost_pcm_pts_to r x)
    (fun v -> ghost_pcm_pts_to r (f v))

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_ghost unit
    (ghost_pcm_pts_to r x)
    (fun _ -> ghost_pcm_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    (ghost_pcm_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pcm_pts_to r v0 ** ghost_pcm_pts_to r v1)

val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    (ghost_pcm_pts_to r v0 ** ghost_pcm_pts_to r v1)
    (fun _ -> ghost_pcm_pts_to r (op pcm v0 v1))

// Finally, a big escape hatch for introducing architecture/backend-specific
// atomic operations from proven stt specifications
[@@warn_on_use "as_atomic is a an assumption"]
val as_atomic (#a:Type u#0) (pre:vprop) (post:a -> vprop)
              (pf:stt a pre post)
: stt_atomic a emp_inames pre post
