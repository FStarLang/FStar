(*
   Copyright 2024 Microsoft Research

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

module PulseCore.MemoryAlt
open FStar.Ghost
open FStar.PCM
module PST = PulseCore.HoareStateMonad
module U = FStar.Universe
module CM = FStar.Algebra.CommMonoid
module B = PulseCore.BaseHeapSig

(**** Basic memory properties *)

(** Abstract type of memories *)
let mem : Type u#(a + 4) = B.mem

let is_ghost_action (m0 m1:mem u#a) : prop = B.is_ghost_action m0 m1
let maybe_ghost_action (b:bool) (m0 m1:mem u#a) = b ==> is_ghost_action m0 m1

val ghost_action_preorder (_:unit)
  : Lemma (FStar.Preorder.preorder_rel is_ghost_action)

(**** Separation logic *)

(** The type of separation logic propositions. Based on Steel.Heap.slprop *)
[@@erasable]
let slprop : Type u#(a + 4) = B.slprop //invariant predicates, i --> p, live in u#a+4

(** Interpreting mem assertions as memory predicates *)
let interp (p:slprop u#a) (m:mem u#a) : prop = B.interp p m

(** Equivalence relation on slprops is just equivalence of their interpretations *)
val equiv (p1 p2:slprop u#a) : prop

(**
  An extensional equivalence principle for slprop
 *)

val slprop_extensionality (p q:slprop u#a)
  : Lemma
    (requires p `equiv` q)
    (ensures p == q)

val slprop_equiv_refl (p:slprop)
  : Lemma (p `equiv` p)
          [SMTPat (equiv p p)]
          
(** A memory maps a [ref]erence to its associated value *)
val core_ref : Type u#0

let ref (a:Type u#a) (pcm:pcm a) : Type u#0 = core_ref

(** [null] is a specific reference, that is not associated to any value
*)
val core_ref_null : core_ref

(** [null] is a specific reference, that is not associated to any value
*)
let null (#a:Type u#a) (#pcm:pcm a) : ref a pcm = core_ref_null

val core_ref_is_null (r:core_ref) : b:bool { b <==> r == core_ref_null }

(** Checking whether [r] is the null pointer is decidable through [is_null]
*)
let is_null (#a:Type u#a) (#pcm:pcm a) (r:ref a pcm) : (b:bool{b <==> r == null}) = core_ref_is_null r

(** All the standard connectives of separation logic, based on [Steel.Heap] *)
let emp : slprop u#a = B.emp
let pure (p:prop) : slprop u#a = B.pure p
let star  (p1 p2:slprop u#a) : slprop u#a = B.star p1 p2

(***** Properties of separation logic equivalence *)

val emp_unit (p:slprop)
  : Lemma (p `equiv` (p `star` emp))


(** Equivalence of pure propositions is the equivalence of the underlying propositions *)
val pure_equiv (p q:prop)
  : Lemma ((p <==> q) ==> (pure p `equiv` pure q))

(** And the interpretation of pure propositions is their underlying propositions *)

val pure_true_emp (_:unit)
  : Lemma (pure True `equiv` emp)

(***** Properties of the separating conjunction *)
val star_commutative (p1 p2:slprop)
  : Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))

val star_associative (p1 p2 p3:slprop)
  : Lemma ((p1 `star` (p2 `star` p3))
           `equiv`
           ((p1 `star` p2) `star` p3))

val star_congruence (p1 p2 p3 p4:slprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))

val full_mem_pred: mem -> prop
let full_mem = m:mem{full_mem_pred m}

(**** Actions *)

let _PST 
  (a:Type u#a)
  (maybe_ghost:bool)
  (expects:slprop u#m)
  (provides: a -> slprop u#m)
  (frame:slprop u#m)
= PST.st #(full_mem u#m) a
    (requires fun m0 ->
        interp (expects `star` frame) m0)
    (ensures fun m0 x m1 ->
        maybe_ghost_action maybe_ghost m0 m1 /\
        interp (expects `star` frame) m0 /\  //TODO: fix the effect so as not to repeat this
        interp (provides x `star` frame) m1)

(** An action is just a thunked computation in [MstTot] that takes a frame as argument *)
let _pst_action_except 
    (a:Type u#a)
    (maybe_ghost:bool)
    (expects:slprop u#um)
    (provides: a -> slprop u#um)
 : Type u#(max a (um + 4)) 
 = frame:slprop -> _PST a maybe_ghost expects provides frame

let pst_action_except (a:Type u#a) (expects:slprop u#um) (provides: a ->  slprop u#um) =
  _pst_action_except a false expects provides

let pst_ghost_action_except (a:Type u#a) (expects:slprop u#um) (provides: a -> slprop u#um) =
  _pst_action_except a true expects provides


(* Some generic actions and combinators *)

let non_info a = x:erased a -> y:a { reveal x == y}

val lift_ghost
      (#a:Type)
      #p #q
      (ni_a:non_info a)
      (f:erased (pst_ghost_action_except a p q))
  : pst_ghost_action_except a p q

(* Concrete references to "small" types *)
val pts_to (#a:Type u#(a+1)) (#pcm:_) (r:ref a pcm) (v:a) : slprop u#a

(** Splitting a permission on a composite resource into two separate permissions *)
val split_action
  (#a:Type u#(a + 1))
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 `star` pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val gather_action
  (#a:Type u#(a + 1))
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
: pst_ghost_action_except (squash (composable pcm v0 v1))
    (pts_to r v0 `star` pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))

val alloc_action (#a:Type u#(a + 1)) (#pcm:pcm a) (x:a{pcm.refine x})
: pst_action_except (ref a pcm)
    emp
    (fun r -> pts_to r x)

val select_refine (#a:Type u#(a + 1)) (#p:pcm a)
                  (r:ref a p)
                  (x:erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  FStar.PCM.frame_compatible p x v y})))
: pst_action_except (v:a{compatible p x v /\ p.refine v})
    (pts_to r x)
    (fun v -> pts_to r (f v))

val upd_gen (#a:Type u#(a + 1)) (#p:pcm a) (r:ref a p) (x y:Ghost.erased a)
            (f:FStar.PCM.frame_preserving_upd p x y)
: pst_action_except unit
    (pts_to r x)
    (fun _ -> pts_to r y)

val pts_to_not_null_action 
      (#a:Type u#(a + 1)) (#pcm:pcm a)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r)))
    (pts_to r v)
    (fun _ -> pts_to r v)

(* Ghost references to "small" types *)
[@@erasable]
val core_ghost_ref : Type0
let ghost_ref (#a:Type u#a) (p:pcm a) : Type0 = core_ghost_ref
val ghost_pts_to (#a:Type u#(a+1)) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop u#a

val ghost_alloc
    (#a:Type u#(a + 1))
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    emp
    (fun r -> ghost_pts_to r x)

val ghost_read
    (#a:Type u#(a + 1))
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit
    (ghost_pts_to r x)
    (fun _ -> ghost_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 `star` ghost_pts_to r v1)

val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1))
    (ghost_pts_to r v0 `star` ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))

(* Concrete references to "big" types *)
val big_pts_to (#a:Type u#(a + 2)) (#pcm:_) (r:ref a pcm) (v:a) : slprop u#a

(** Splitting a permission on a composite resource into two separate permissions *)
val big_split_action
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit
    (big_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_pts_to r v0 `star` big_pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val big_gather_action
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a)
: pst_ghost_action_except (squash (composable pcm v0 v1))
    (big_pts_to r v0 `star` big_pts_to r v1)
    (fun _ -> big_pts_to r (op pcm v0 v1))

val big_alloc_action
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (x:a{pcm.refine x})
: pst_action_except (ref a pcm)
    emp
    (fun r -> big_pts_to r x)

val big_select_refine
      (#a:Type u#(a + 2))
      (#p:pcm a)
      (r:ref a p)
      (x:erased a)
      (f:(v:a{compatible p x v}
          -> GTot (y:a{compatible p y v /\
                      FStar.PCM.frame_compatible p x v y})))
: pst_action_except (v:a{compatible p x v /\ p.refine v})
    (big_pts_to r x)
    (fun v -> big_pts_to r (f v))

val big_upd_gen
    (#a:Type u#(a + 2))
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_action_except unit
    (big_pts_to r x)
    (fun _ -> big_pts_to r y)

val big_pts_to_not_null_action 
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r)))
    (big_pts_to r v)
    (fun _ -> big_pts_to r v)

val big_ghost_pts_to (#a:Type u#(a + 2)) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop u#a

val big_ghost_alloc
    (#a:Type u#(a + 2))
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    emp 
    (fun r -> big_ghost_pts_to r x)

val big_ghost_read
    (#a:Type u#(a + 2))
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    (big_ghost_pts_to r x)
    (fun v -> big_ghost_pts_to r (f v))

val big_ghost_write
    (#a:Type u#(a + 2))
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit
    (big_ghost_pts_to r x)
    (fun _ -> big_ghost_pts_to r y)

val big_ghost_share
    (#a:Type u#(a + 2))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit
    (big_ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)

val big_ghost_gather
    (#a:Type u#(a + 2))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1))
    (big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)
    (fun _ -> big_ghost_pts_to r (op pcm v0 v1))

(* References for objects in universes a+2, "non-boxable" pts_to *)
val nb_pts_to (#a:Type u#(a + 3)) (#pcm:_) (r:ref a pcm) (v:a) : slprop u#a

(** Splitting a permission on a composite resource into two separate permissions *)
val nb_split_action
      (#a:Type u#(a + 3))
      (#pcm:pcm a)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit
    (nb_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_pts_to r v0 `star` nb_pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val nb_gather_action
      (#a:Type u#(a + 3))
      (#pcm:pcm a)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a)
: pst_ghost_action_except (squash (composable pcm v0 v1))
    (nb_pts_to r v0 `star` nb_pts_to r v1)
    (fun _ -> nb_pts_to r (op pcm v0 v1))

val nb_alloc_action
      (#a:Type u#(a + 3))
      (#pcm:pcm a)
      (x:a{pcm.refine x})
: pst_action_except (ref a pcm)
    emp
    (fun r -> nb_pts_to r x)

val nb_select_refine
      (#a:Type u#(a + 3))
      (#p:pcm a)
      (r:ref a p)
      (x:erased a)
      (f:(v:a{compatible p x v}
          -> GTot (y:a{compatible p y v /\
                      FStar.PCM.frame_compatible p x v y})))
: pst_action_except (v:a{compatible p x v /\ p.refine v})
    (nb_pts_to r x)
    (fun v -> nb_pts_to r (f v))

val nb_upd_gen
    (#a:Type u#(a + 3))
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_action_except unit
    (nb_pts_to r x)
    (fun _ -> nb_pts_to r y)

val nb_pts_to_not_null_action 
      (#a:Type u#(a + 3))
      (#pcm:pcm a)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r)))
    (nb_pts_to r v)
    (fun _ -> nb_pts_to r v)

val nb_ghost_pts_to (#a:Type u#(a + 3)) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop u#a

val nb_ghost_alloc
    (#a:Type u#(a + 3))
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    emp 
    (fun r -> nb_ghost_pts_to r x)

val nb_ghost_read
    (#a:Type u#(a + 3))
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    (nb_ghost_pts_to r x)
    (fun v -> nb_ghost_pts_to r (f v))

val nb_ghost_write
    (#a:Type u#(a + 3))
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit
    (nb_ghost_pts_to r x)
    (fun _ -> nb_ghost_pts_to r y)

val nb_ghost_share
    (#a:Type u#(a + 3))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit
    (nb_ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_ghost_pts_to r v0 `star` nb_ghost_pts_to r v1)

val nb_ghost_gather
    (#a:Type u#(a + 3))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1))
    (nb_ghost_pts_to r v0 `star` nb_ghost_pts_to r v1)
    (fun _ -> nb_ghost_pts_to r (op pcm v0 v1))

