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

module PulseCore.Atomic

open FStar.Ghost

open PulseCore.InstantiatedSemantics
open PulseCore.Action
open PulseCore.Observability

(* stt_unobservable a opens pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes an unobservable atomic step
   potentially opening invariants in `opens`
   and returns `x:a`
   such that the final state satisfies `post x` *)
[@@extract_as_impure_effect]
val stt_atomic
    (a:Type u#a)
    (#obs:observability)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max 4 a)

val return_atomic
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt_atomic a #Neutral emp_inames (p x) (fun r -> p r ** pure (r == x))

val return_atomic_noeq
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

val lift_observability 
    (#a:Type u#a)
    (#obs #obs':_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e1:stt_atomic a #obs opens pre post)
: stt_atomic a #(join_obs obs obs') opens pre post

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

val frame_atomic
    (#a:Type u#a)
    (#obs: observability)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
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

val sub_invs_stt_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens1 #opens2:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens1 pre post)
    (_ : squash (inames_subset opens1 opens2))
: stt_atomic a #obs opens2 pre post

(* stt_ghost a opens pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes a single ghost atomic step (i.e. a step that does not modify the heap, and does not get extracted)
   potentially opening invariants in `opens`
   and returns `x:a`
   such that the final state satisfies `post x` *)
[@@ erasable]
val stt_ghost
    (a:Type u#a)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max 4 a)

val return_ghost
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt_ghost a emp_inames (p x) (fun r -> p r ** pure (r == x))

val return_ghost_noeq
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt_ghost a emp_inames (p x) p

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

type non_informative_witness (a:Type u#a) =
  x:Ghost.erased a -> y:a{y == Ghost.reveal x}

val lift_ghost_neutral
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_ghost a opens pre post)
    (reveal_a:non_informative_witness a)
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
    (#pre:slprop)
    (#post:a -> slprop)
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

val sub_invs_stt_ghost
    (#a:Type u#a)
    (#opens1 #opens2:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_ghost a opens1 pre post)
    (_ : squash (inames_subset opens1 opens2))
: stt_ghost a opens2 pre post

val noop (p:slprop)
: stt_ghost unit emp_inames p (fun _ -> p)

val intro_pure (p:prop) (pf:squash p)
: stt_ghost unit emp_inames emp (fun _ -> pure p)

val elim_pure (p:prop)
: stt_ghost (squash p) emp_inames (pure p) (fun _ -> emp)

val intro_exists (#a:Type u#a) (p:a -> slprop) (x:erased a)
: stt_ghost unit emp_inames (p x) (fun _ -> exists* x. p x)

val elim_exists (#a:Type u#a) (p:a -> slprop)
: stt_ghost (erased a) emp_inames (exists* x. p x) (fun x -> p x)

val ghost_reveal (a:Type) (x:erased a)
  : stt_ghost a emp_inames emp (fun y -> pure (reveal x == y))

//////////////////////////////////////////////////////////////////

val dup_inv (i:iref) (p:slprop)
  : stt_ghost unit emp_inames (inv i p) (fun _ -> (inv i p) ** (inv i p))

val new_invariant (p:slprop)
  : stt_ghost iref emp_inames p (fun i -> inv i p)

val fresh_invariant (ctx:list iref) (p:slprop)
: stt_ghost (i:iref { i `fresh_wrt` ctx })
            emp_inames
            p
            (fun i -> inv i p)

val with_invariant
    (#a:Type)
    (#obs:_)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:iref { not (mem_inv f_opens i) })
    ($f:unit -> stt_atomic a #obs f_opens
                           (later p ** fp)
                           (fun x -> later p ** fp' x))
: stt_atomic a #obs (add_inv f_opens i) ((inv i p) ** fp) (fun x -> (inv i p) ** fp' x)

val with_invariant_g
    (#a:Type)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:iref { not (mem_inv f_opens i) })
    ($f:unit -> stt_ghost a f_opens
                            (later p ** fp)
                            (fun x -> later p ** fp' x))
: stt_ghost a (add_inv f_opens i) ((inv i p) ** fp) (fun x -> (inv i p) ** fp' x)

// val distinct_invariants_have_distinct_names
//     (#p #q:slprop)
//     (i j:iref)
//     (_:squash (p =!= q))
// : stt_ghost
//     (squash (i =!= j))
//     emp_inames
//     ((inv i p) ** (inv j q))
//     (fun _ -> (inv i p) ** (inv j q))

val invariant_name_identifies_invariant
      (p q:slprop)
      (i:iref)
      (j:iref { i == j })
: stt_ghost
    unit
    emp_inames
    (inv i p ** inv j q)
    (fun _ -> inv i p ** inv j q ** InstantiatedSemantics.equiv p q)

////////////////////////////////////////////////////////////////////////
// References
////////////////////////////////////////////////////////////////////////
open FStar.PCM
module PP = PulseCore.Preorder

val pts_to_not_null
    (#a:Type u#1)
    (#p:FStar.PCM.pcm a)
    (r:ref a p)
    (v:a)
: stt_ghost (squash (not (is_ref_null r)))
    emp_inames
    (pts_to r v)
    (fun _ -> pts_to r v)

val alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: stt_atomic (ref a pcm)
    #Observable
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
: stt_atomic (v:a{compatible p x v /\ p.refine v})
    #Observable
    emp_inames
    (pts_to r x)
    (fun v -> pts_to r (f v))

val write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_atomic unit
    #Observable
    emp_inames
    (pts_to r x)
    (fun _ -> pts_to r y)

val share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 ** pts_to r v1)

val gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (pts_to r v0 ** pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))

////////////////////////////////////////////////////////////////////////
// Ghost References
////////////////////////////////////////////////////////////////////////
val ghost_alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: stt_ghost (ghost_ref pcm)
    emp_inames
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
: stt_ghost (erased (v:a{compatible p x v /\ p.refine v}))
    emp_inames
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_ghost unit
    emp_inames
    (ghost_pts_to r x)
    (fun _ -> ghost_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 ** ghost_pts_to r v1)

val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (ghost_pts_to r v0 ** ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))

////////////////////////////////////////////////////////////////////////
// Big References
////////////////////////////////////////////////////////////////////////

val big_pts_to_not_null
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:ref a p)
    (v:a)
: stt_ghost (squash (not (is_ref_null r)))
    emp_inames
    (big_pts_to r v)
    (fun _ -> big_pts_to r v)

val big_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: stt_atomic (ref a pcm)
    #Observable
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
: stt_atomic (v:a{compatible p x v /\ p.refine v})
    #Observable
    emp_inames
    (big_pts_to r x)
    (fun v -> big_pts_to r (f v))

val big_write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_atomic unit
    #Observable
    emp_inames
    (big_pts_to r x)
    (fun _ -> big_pts_to r y)

val big_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (big_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_pts_to r v0 ** big_pts_to r v1)

val big_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (big_pts_to r v0 ** big_pts_to r v1)
    (fun _ -> big_pts_to r (op pcm v0 v1))

val big_ghost_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: stt_ghost (ghost_ref pcm)
    emp_inames
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
: stt_ghost (erased (v:a{compatible p x v /\ p.refine v}))
    emp_inames
    (big_ghost_pts_to r x)
    (fun v -> big_ghost_pts_to r (f v))

val big_ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_ghost unit
    emp_inames
    (big_ghost_pts_to r x)
    (fun _ -> big_ghost_pts_to r y)

val big_ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (big_ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_ghost_pts_to r v0 ** big_ghost_pts_to r v1)

val big_ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (big_ghost_pts_to r v0 ** big_ghost_pts_to r v1)
    (fun _ -> big_ghost_pts_to r (op pcm v0 v1))


////////////////////////////////////////////////////////////////////////
// Non-boxable References
////////////////////////////////////////////////////////////////////////

val nb_pts_to_not_null
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:ref a p)
    (v:a)
: stt_ghost (squash (not (is_ref_null r)))
    emp_inames
    (nb_pts_to r v)
    (fun _ -> nb_pts_to r v)

val nb_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: stt_atomic (ref a pcm)
    #Observable
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
: stt_atomic (v:a{compatible p x v /\ p.refine v})
    #Observable
    emp_inames
    (nb_pts_to r x)
    (fun v -> nb_pts_to r (f v))

val nb_write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_atomic unit
    #Observable
    emp_inames
    (nb_pts_to r x)
    (fun _ -> nb_pts_to r y)

val nb_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (nb_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_pts_to r v0 ** nb_pts_to r v1)

val nb_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (nb_pts_to r v0 ** nb_pts_to r v1)
    (fun _ -> nb_pts_to r (op pcm v0 v1))

val nb_ghost_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: stt_ghost (ghost_ref pcm)
    emp_inames
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
: stt_ghost (erased (v:a{compatible p x v /\ p.refine v}))
    emp_inames
    (nb_ghost_pts_to r x)
    (fun v -> nb_ghost_pts_to r (f v))

val nb_ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_ghost unit
    emp_inames
    (nb_ghost_pts_to r x)
    (fun _ -> nb_ghost_pts_to r y)

val nb_ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (nb_ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_ghost_pts_to r v0 ** nb_ghost_pts_to r v1)

val nb_ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (nb_ghost_pts_to r v0 ** nb_ghost_pts_to r v1)
    (fun _ -> nb_ghost_pts_to r (op pcm v0 v1))


val drop (p:slprop)
: stt_ghost unit emp_inames p (fun _ -> emp)