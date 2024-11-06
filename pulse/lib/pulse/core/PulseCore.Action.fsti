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

module PulseCore.Action

module S = FStar.Set
module I = PulseCore.InstantiatedSemantics
module PP = PulseCore.Preorder

open FStar.PCM
open FStar.Ghost

open PulseCore.InstantiatedSemantics

type reifiability =
 | Ghost
 | Atomic

let ( ^^ ) (r1 r2 : reifiability) : reifiability =
  if r1 = r2 then r1
  else Atomic

[@@ erasable]
val iref : Type0
val deq_iref : FStar.GhostSet.decide_eq iref
let inames = FStar.GhostSet.set iref
let singleton (i:iref) : inames = GhostSet.singleton deq_iref i
let emp_inames : inames = GhostSet.empty

let join_inames (is1 is2 : inames) : inames =
  GhostSet.union is1 is2

let inames_subset (is1 is2 : inames) : Type0 =
  GhostSet.subset is1 is2

let (/!) (is1 is2 : inames) : Type0 =
  GhostSet.disjoint is1 is2

unfold
let inames_disj (ictx:inames) : Type = is:inames{is /! ictx}

val act 
    (a:Type u#a)
    (tag:reifiability)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max a 4)

val return 
    (#a:Type u#a)
    (#r:_)
    (#post:a -> slprop)
    (x:a)
: act a r emp_inames (post x) post

val bind
     (#a:Type u#a)
     (#b:Type u#b)
     (#r:reifiability)
     (#opens:inames)
     (#pre1 #post1 #post2:_)
     (f:act a r opens pre1 post1)
     (g:(x:a -> act b r opens (post1 x) post2))
: act b r opens pre1 post2

val frame
     (#a:Type u#a)
     (#r:reifiability)
     (#opens:inames)
     (#pre #post #frame:_)
     (f:act a r opens pre post)
: act a r opens (pre ** frame) (fun x -> post x ** frame)

val lift_ghost_atomic
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens:inames)
    (f:act a Ghost opens pre post)
: act a Atomic opens pre post

val weaken 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#r0 #r1:reifiability)
    (#opens opens':inames)
    (f:act a r0 opens pre post)
: act a (r0 ^^ r1) (GhostSet.union opens opens') pre post

val sub 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#r:reifiability)
    (#opens:inames)
    (pre':slprop { slprop_equiv pre pre' })
    (post':a -> slprop { forall x. slprop_equiv (post x) (post' x) })
    (f:act a r opens pre post)
: act a r opens pre' post'

val lift (#a:Type u#100) #r #opens (#pre:slprop) (#post:a -> slprop)
         (m:act a r opens pre post)
: I.stt a pre post

val lift0 (#a:Type u#0) #r #opens #pre #post
          (m:act a r opens pre post)
: I.stt a pre post

val lift1 (#a:Type u#1) #r #opens #pre #post
          (m:act a r opens pre post)
: I.stt a pre post

val lift2 (#a:Type u#2) #r #opens #pre #post
          (m:act a r opens pre post)
: I.stt a pre post

val lift3 (#a:Type u#3) #r #opens #pre #post
          (m:act a r opens pre post)
: I.stt a pre post

//////////////////////////////////////////////////////////////////////
// Invariants
//////////////////////////////////////////////////////////////////////

let add_inv (e:inames) (i:iref) : inames = GhostSet.union (singleton i) e
let mem_inv (e:inames) (i:iref) : GTot bool = GhostSet.mem i e

val inv (i:iref) (p:slprop) : slprop

val dup_inv (i:iref) (p:slprop)
  : act unit Ghost emp_inames (inv i p) (fun _ -> (inv i p) ** (inv i p))

val new_invariant (p:slprop)
: act iref Ghost emp_inames p (fun i -> inv i p)

let fresh_wrt (i:iref)
              (ctx:list iref)
: prop
= forall i'. List.Tot.memP i' ctx ==> i' =!= i

val fresh_invariant (ctx:list iref) (p:slprop)
: act (i:iref { i `fresh_wrt` ctx }) Ghost emp_inames p (fun i -> inv i p)

val with_invariant
    (#a:Type)
    (#r:_)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:iref { not (mem_inv f_opens i) })
    (f:unit -> act a r f_opens (later p ** fp) (fun x -> later p ** fp' x))
: act a r (add_inv f_opens i) ((inv i p) ** fp) (fun x -> (inv i p) ** fp' x)

// val distinct_invariants_have_distinct_names
//     (#p:slprop)
//     (#q:slprop)
//     (i j:iref)
//     (_:squash (p =!= q))
// : act (squash (i =!= j))
//       Ghost
//       emp_inames 
//       ((inv i p) ** (inv j q))
//       (fun _ -> (inv i p) ** (inv j q))

val invariant_name_identifies_invariant
      (p q:slprop)
      (i:iref)
: act unit
      Ghost
      emp_inames
      (inv i p ** inv i q)
      (fun _ -> inv i p ** inv i q ** later (equiv p q))

////////////////////////////////////////////////////////////////////////
// later and credits
////////////////////////////////////////////////////////////////////////
val later_intro (p:slprop)
: act unit Ghost emp_inames p (fun _ -> later p)

val later_elim (p:slprop)
: act unit Ghost emp_inames (later p ** later_credit 1) (fun _ -> p)

val later_elim_timeless (p:slprop { timeless p })
: act unit Ghost emp_inames (later p) (fun _ -> p)

val buy (n:erased nat)
: stt unit emp (fun _ -> later_credit n)

////////////////////////////////////////////////////////////////////////
// References
////////////////////////////////////////////////////////////////////////
val core_ref : Type u#0
val core_ref_null : core_ref
val is_core_ref_null (r:core_ref) : b:bool { b <==> r == core_ref_null }

let ref (a:Type u#a) (p:pcm a) : Type u#0 = core_ref
let ref_null (#a:Type u#a) (p:pcm a) : ref a p = core_ref_null

let is_ref_null (#a:Type) (#p:FStar.PCM.pcm a) (r:ref a p)
: b:bool { b <==> r == ref_null p }
= is_core_ref_null r

val pts_to (#a:Type u#1) (#p:pcm a) (r:ref a p) (v:a) : slprop

val timeless_pts_to
    (#a:Type u#1)
    (#p:pcm a)
    (r:ref a p)
    (v:a)
: Lemma (timeless (pts_to r v))

val pts_to_not_null (#a:Type) (#p:FStar.PCM.pcm a) (r:ref a p) (v:a)
: act (squash (not (is_ref_null r)))
    Ghost
    emp_inames 
    (pts_to r v)
    (fun _ -> pts_to r v)

val alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: act (ref a pcm)
      Atomic
      emp_inames
      emp
      (fun r -> pts_to r x)

val read
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (v:a{compatible p x v /\ p.refine v})
      Atomic
      emp_inames
      (pts_to r x)
      (fun v -> pts_to r (f v))

val write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit
    Atomic
    emp_inames
    (pts_to r x)
    (fun _ -> pts_to r y)

val share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit
    Ghost
    emp_inames
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 ** pts_to r v1)

val gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1))
    Ghost
    emp_inames
    (pts_to r v0 ** pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))

///////////////////////////////////////////////////////////////////
// Big references
///////////////////////////////////////////////////////////////////

val big_pts_to (#a:Type u#2) (#p:pcm a) (r:ref a p) (v:a) : slprop


val timeless_big_pts_to
    (#a:Type u#2)
    (#p:pcm a)
    (r:ref a p)
    (v:a)
: Lemma (timeless (big_pts_to r v))

val big_pts_to_not_null (#a:Type) (#p:FStar.PCM.pcm a) (r:ref a p) (v:a)
: act (squash (not (is_ref_null r)))
    Ghost
    emp_inames 
    (big_pts_to r v)
    (fun _ -> big_pts_to r v)

val big_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: act (ref a pcm)
      Atomic
      emp_inames
      emp
      (fun r -> big_pts_to r x)

val big_read
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (v:a{compatible p x v /\ p.refine v})
      Atomic
      emp_inames
      (big_pts_to r x)
      (fun v -> big_pts_to r (f v))

val big_write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit
    Atomic
    emp_inames
    (big_pts_to r x)
    (fun _ -> big_pts_to r y)

val big_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit
    Ghost
    emp_inames
    (big_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_pts_to r v0 ** big_pts_to r v1)

val big_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1))
    Ghost
    emp_inames
    (big_pts_to r v0 ** big_pts_to r v1)
    (fun _ -> big_pts_to r (op pcm v0 v1))

///////////////////////////////////////////////////////////////////
// Non-boxable references
///////////////////////////////////////////////////////////////////

val nb_pts_to (#a:Type u#3) (#p:pcm a) (r:ref a p) (v:a) : slprop


val timeless_nb_pts_to
    (#a:Type u#3)
    (#p:pcm a)
    (r:ref a p)
    (v:a)
: Lemma (timeless (nb_pts_to r v))

val nb_pts_to_not_null (#a:Type) (#p:FStar.PCM.pcm a) (r:ref a p) (v:a)
: act (squash (not (is_ref_null r)))
    Ghost
    emp_inames 
    (nb_pts_to r v)
    (fun _ -> nb_pts_to r v)

val nb_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: act (ref a pcm)
      Atomic
      emp_inames
      emp
      (fun r -> nb_pts_to r x)

val nb_read
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (v:a{compatible p x v /\ p.refine v})
      Atomic
      emp_inames
      (nb_pts_to r x)
      (fun v -> nb_pts_to r (f v))

val nb_write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit
    Atomic
    emp_inames
    (nb_pts_to r x)
    (fun _ -> nb_pts_to r y)

val nb_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit
    Ghost
    emp_inames
    (nb_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_pts_to r v0 ** nb_pts_to r v1)

val nb_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1))
    Ghost
    emp_inames
    (nb_pts_to r v0 ** nb_pts_to r v1)
    (fun _ -> nb_pts_to r (op pcm v0 v1))

///////////////////////////////////////////////////////////////////
// pure
///////////////////////////////////////////////////////////////////
val pure_true ()
: slprop_equiv (pure True) emp

val intro_pure (p:prop) (pf:squash p)
: act unit Ghost emp_inames emp (fun _ -> pure p)

val elim_pure (p:prop)
: act (squash p) Ghost emp_inames (pure p) (fun _ -> emp)

///////////////////////////////////////////////////////////////////
// exists*
///////////////////////////////////////////////////////////////////
val intro_exists (#a:Type u#a) (p:a -> slprop) (x:erased a)
: act unit Ghost emp_inames (p x) (fun _ -> exists* x. p x)

val elim_exists (#a:Type u#a) (p:a -> slprop)
: act (erased a) Ghost emp_inames (exists* x. p x) (fun x -> p x)

///////////////////////////////////////////////////////////////////
// Other utils
///////////////////////////////////////////////////////////////////
val drop (p:slprop)
: act unit Ghost emp_inames p (fun _ -> emp)

////////////////////////////////////////////////////////////////////////
// Ghost References
////////////////////////////////////////////////////////////////////////
[@@erasable]
val core_ghost_ref : Type u#0
let ghost_ref (#a:Type u#a) (p:pcm a) : Type u#0 = core_ghost_ref
val ghost_pts_to (#a:Type u#1) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop

val timeless_ghost_pts_to
    (#a:Type u#1)
    (#p:pcm a)
    (r:ghost_ref p)
    (v:a)
: Lemma (timeless (ghost_pts_to r v))

val ghost_alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: act (ghost_ref pcm) Ghost emp_inames
    emp 
    (fun r -> ghost_pts_to r x)

val ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (erased (v:a{compatible p x v /\ p.refine v})) Ghost emp_inames
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit Ghost emp_inames 
    (ghost_pts_to r x)
    (fun _ -> ghost_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit Ghost emp_inames
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 ** ghost_pts_to r v1)

val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1)) Ghost emp_inames
    (ghost_pts_to r v0 ** ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))

val big_ghost_pts_to (#a:Type u#2) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop


val timeless_big_ghost_pts_to
    (#a:Type u#2)
    (#p:pcm a)
    (r:ghost_ref p)
    (v:a)
: Lemma (timeless (big_ghost_pts_to r v))

val big_ghost_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: act (ghost_ref pcm) Ghost emp_inames
    emp 
    (fun r -> big_ghost_pts_to r x)

val big_ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (erased (v:a{compatible p x v /\ p.refine v})) Ghost emp_inames
    (big_ghost_pts_to r x)
    (fun v -> big_ghost_pts_to r (f v))

val big_ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit Ghost emp_inames 
    (big_ghost_pts_to r x)
    (fun _ -> big_ghost_pts_to r y)

val big_ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit Ghost emp_inames
    (big_ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_ghost_pts_to r v0 ** big_ghost_pts_to r v1)

val big_ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1)) Ghost emp_inames
    (big_ghost_pts_to r v0 ** big_ghost_pts_to r v1)
    (fun _ -> big_ghost_pts_to r (op pcm v0 v1))

// Non-boxable ghost references
val nb_ghost_pts_to (#a:Type u#3) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop


val timeless_nb_ghost_pts_to
    (#a:Type u#3)
    (#p:pcm a)
    (r:ghost_ref p)
    (v:a)
: Lemma (timeless (nb_ghost_pts_to r v))

val nb_ghost_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: act (ghost_ref pcm) Ghost emp_inames
    emp 
    (fun r -> nb_ghost_pts_to r x)

val nb_ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (erased (v:a{compatible p x v /\ p.refine v})) Ghost emp_inames
    (nb_ghost_pts_to r x)
    (fun v -> nb_ghost_pts_to r (f v))

val nb_ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit Ghost emp_inames 
    (nb_ghost_pts_to r x)
    (fun _ -> nb_ghost_pts_to r y)

val nb_ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit Ghost emp_inames
    (nb_ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_ghost_pts_to r v0 ** nb_ghost_pts_to r v1)

val nb_ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1)) Ghost emp_inames
    (nb_ghost_pts_to r v0 ** nb_ghost_pts_to r v1)
    (fun _ -> nb_ghost_pts_to r (op pcm v0 v1))


////////////////////////////////////////////////////////////////////////
let non_informative a = x:erased a -> y:a { reveal x == y}

val lift_erased 
    (#a:Type)
    (ni_a:non_informative a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (f:erased (act a Ghost opens pre post))
: act a Ghost opens pre post
