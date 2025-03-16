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

module Sem = PulseCore.Semantics
module Sep = PulseCore.IndirectionTheorySep
module ITA = PulseCore.IndirectionTheoryActions
module Mem = PulseCore.MemoryAlt
module I = PulseCore.InstantiatedSemantics
module F = FStar.FunctionalExtensionality
module ST = PulseCore.HoareStateMonad
module Set = FStar.GhostSet
module U = FStar.Universe
friend PulseCore.InstantiatedSemantics

open FStar.PCM
open FStar.Ghost
open PulseCore.IndirectionTheorySep
open PulseCore.InstantiatedSemantics

//////////////////////////////////////////////////////
// An abstraction on top of memory actions
//////////////////////////////////////////////////////

// (* The type of semantic actions, does not distinguish reifiability *)
// let action
//     (a:Type u#a)
//     (except:inames)
//     (pre:slprop)
//     (post:a -> slprop)
// : Type u#(max a 4)
// = frame:slprop ->
//   Sem.pst_sep_aux state
//     (inames_ok except)
//     (state0 except).invariant
//     a 
//     (pre `star` frame)
//     (fun x -> post x `star` frame)


// let action_as_mem_action
//         (a:Type u#a)
//         (except:inames)
//         (pre:slprop)
//         (post: a -> slprop) 
//         (act:action a except pre post)
// : Mem.pst_action_except a except pre post
// = fun frame ->
//     let m
//       : PST.st #(full_mem)
//                 a
//                 (fun s0 -> 
//                     inames_ok except s0 /\
//                     interp ((pre `star` mem_invariant except s0) `star` frame) s0)
//                 (fun s0 x s1 ->
//                     inames_ok except s1 /\
//                     interp ((post x `star` mem_invariant except s1) `star` frame) s1)
//       = PST.weaken (act frame)
//     in
//     PST.weaken m
 
let inames_ok_empty (m:Sep.mem)
: Lemma
  (ensures Sep.inames_ok GhostSet.empty m)
  [SMTPat (Sep.inames_ok GhostSet.empty m)]
= Sep.inames_ok_empty m

let stt_of_action (#a:Type u#100) #ak #pre #post (m:ITA._act_except a ak GhostSet.empty pre post)
: stt a pre post
= let step (frame:slprop)
    : Sem.st_sep state a (pre `star` frame) (fun x -> post x `star` frame)
    = ST.weaken (m frame)
  in
  let action : Sem.action state a = {pre=pre; post=F.on_dom _ post; step} in
  let m : Sem.m a pre _ = Sem.act action in
  fun _ -> m

let stt_of_action0 (#a:Type u#0) #ak #pre #post (m:ITA._act_except a ak GhostSet.empty pre post)
: stt a pre post
= let step (frame:slprop)
    : Sem.st_sep state a (pre `star` frame) (fun x -> post x `star` frame)
    = m frame
  in
  let action : Sem.action state a = {pre=pre; post=F.on_dom _ post; step} in
  fun _ -> Sem.act_as_m0 action

let stt_of_action4 (#a:Type u#4) #ak #pre #post (m:ITA._act_except a ak GhostSet.empty pre post)
: stt a pre post
= let step (frame:slprop)
    : Sem.st_sep state a (pre `star` frame) (fun x -> post x `star` frame)
    = m frame
  in
  let action : Sem.action state a = {pre=pre; post=F.on_dom _ post; step} in
  let lift : Sem.liftable u#4 u#100 = {
    downgrade_val = (fun t x -> FStar.Universe.downgrade_val x);
    laws = ()
  } in
  fun _ -> Sem.act_as_m_poly u#_ u#4 u#100 lift action


let maybe_ghost (r:reifiability) = r = Ghost

let deq_iref = deq_iref

let as_action_kind : reifiability -> ITA.action_kind = function
  | Ghost -> ITA.GHOST
  | Atomic -> ITA.ATOMIC

let pre_act 
    (a:Type u#a)
    (r:reifiability)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
= ITA._act_except a (as_action_kind r) opens pre post

let map_post #a #b (f: b->a) (post: a->slprop) : b->slprop =
  fun x -> post (f x)

let act 
    (a:Type u#a)
    (r:reifiability)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
= #ictx:inames_disj opens ->
  a':Type u#4 & f:(a'->a) & pre_act a' r ictx pre (map_post f post)

let ghost_action_preorder (_:unit)
  : Lemma (FStar.Preorder.preorder_rel is_ghost_action)
= ()

let return_pre_act
    (#a:Type u#a)
    (#except:inames)
    (#post:a -> slprop)
    (x:a)
: pre_act a Ghost except (post x) post
= ghost_action_preorder ();
  fun frame m0 -> x, m0

let map_pre_act
    (#r:reifiability)
    (#a:Type u#a)
    (#b:Type u#b)
    (#except:inames)
    (#pre #post: _)
    (g:a->b)
    (f:pre_act a r except pre (map_post g post))
: pre_act b r except pre post
= ghost_action_preorder ();
  fun frame m0 ->
    let x, m1 = f frame m0 in
    g x, m1

let bind_pre_act_ghost
     (#a:Type u#a)
     (#b:Type u#b)
     (#except:inames)
     (#pre1 #post1 #post2:_)
     (f:pre_act a Ghost except pre1 post1)
     (g:(x:a -> pre_act b Ghost except (post1 x) post2))
: pre_act b Ghost except pre1 post2
= ghost_action_preorder ();
  fun frame -> ST.bind (f frame) (fun x -> g x frame)

let bind_pre_act_atomic
     (#a:Type u#a)
     (#b:Type u#b)
     (#r1: reifiability)
     (#r2: reifiability { r1 == Ghost \/ r2 == Ghost })
     (#except:inames)
     (#pre1 #post1 #post2:_)
     (f:pre_act a r1 except pre1 post1)
     (g:(x:a -> pre_act b r2 except (post1 x) post2))
: pre_act b Atomic except pre1 post2
= fun frame -> ST.bind (f frame) (fun x -> g x frame)

let frame_pre_act_ghost
     (#a:Type u#a)
     (#except:inames)
     (#pre #post #frame:_)
     (f:pre_act a Ghost except pre post)
: pre_act a Ghost except (pre `star` frame) (fun x -> post x `star` frame)
= fun frame' -> f (frame `star` frame')

let frame_pre_act_atomic
     (#a:Type u#a)
     (#except:inames)
     (#pre #post #frame:_)
     (f:pre_act a Atomic except pre post)
: pre_act a Atomic except (pre `star` frame) (fun x -> post x `star` frame)
= fun frame' -> f (frame `star` frame')

let frame_pre_act
     (#a:Type u#a)
     (#r:reifiability)
     (#except:inames)
     (#pre #post #frame:_)
     (f:pre_act a r except pre post)
: pre_act a r except (pre `star` frame) (fun x -> post x `star` frame)
= match r with
  | Ghost -> frame_pre_act_ghost #a #except #pre #post #frame f
  | Atomic -> frame_pre_act_atomic #a #except #pre #post #frame f

let lift_pre_act_ghost
     (#a:Type u#a)
     (#except:inames)
     (#pre #post:_)
     (f:pre_act a Ghost except pre post)
: pre_act a Atomic except pre post
= f

//////////////////////////////////////////////////////
// Next, reversing the polarity of the inames index
//////////////////////////////////////////////////////

let lift_pre_act0_act (#a: Type u#0) #r #opens #pre #post
  (m: (#ictx:inames_disj opens -> pre_act a r ictx pre post))
: act a r opens pre post
= fun #ictx -> (| U.raise_t a, U.downgrade_val,
    fun m0 frame ->
    let x, m1 = m #ictx m0 frame in
    U.raise_val x, m1 |)

let lift_pre_act1_act (#a: Type u#1) #r #opens #pre #post
  (m: (#ictx:inames_disj opens -> pre_act a r ictx pre post))
: act a r opens pre post
= fun #ictx -> (| U.raise_t u#1 u#4 a, U.downgrade_val,
    fun m0 frame ->
    let x, m1 = m #ictx m0 frame in
    U.raise_val x, m1 |)

let lift_pre_act2_act (#a: Type u#2) #r #opens #pre #post
  (m: (#ictx:inames_disj opens -> pre_act a r ictx pre post))
: act a r opens pre post
= fun #ictx -> (| U.raise_t u#2 u#4 a, U.downgrade_val,
    fun m0 frame ->
    let x, m1 = m #ictx m0 frame in
    U.raise_val x, m1 |)

let lift_pre_act3_act (#a: Type u#3) #r #opens #pre #post
  (m: (#ictx:inames_disj opens -> pre_act a r ictx pre post))
: act a r opens pre post
= fun #ictx -> (| U.raise_t u#3 u#4 a, U.downgrade_val,
    fun m0 frame ->
    let x, m1 = m #ictx m0 frame in
    U.raise_val x, m1 |)

let return 
    (#a:Type u#a)
    (#r:reifiability)
    #opens
    (#post:a -> slprop)
    (x:a)
: act a r opens (post x) post
= fun #ictx -> (| U.raise_t unit, (fun _ -> x), return_pre_act #_ #ictx #(fun _ -> post x) (U.raise_val ()) |)

let bind_ghost
     (#a:Type u#a)
     (#b:Type u#b)
     (#opens:inames)
     (#pre1 #post1 #post2:_)
     (f:act a Ghost opens pre1 post1)
     (g:(x:a -> act b Ghost opens (post1 x) post2))
: act b Ghost opens pre1 post2
= fun #ictx ->
  let (| am, fm, f |) = f #ictx in
  (| x:am & (g (fm x) #ictx)._1,
     (fun (| x, y |) -> (g (fm x) #ictx)._2 y),
     bind_pre_act_ghost #am #_ #ictx #pre1 #(map_post fm post1) #_ f
      (fun x -> map_pre_act #Ghost #_ #(x:am & (g (fm x) #ictx)._1) (fun y -> (| x, y |)) (g (fm x) #ictx)._3) |)

let bind_atomic
     (#a:Type u#a)
     (#b:Type u#b)
     (#r1: reifiability)
     (#r2: reifiability { r1 == Ghost \/ r2 == Ghost })
     (#opens:inames)
     (#pre1 #post1 #post2:_)
     (f:act a r1 opens pre1 post1)
     (g:(x:a -> act b r2 opens (post1 x) post2))
: act b Atomic opens pre1 post2
= fun #ictx ->
  let (| am, fm, f |) = f #ictx in
  (| x:am & (g (fm x) #ictx)._1,
     (fun (| x, y |) -> (g (fm x) #ictx)._2 y),
     bind_pre_act_atomic #am #_ #r1 #r2 #ictx #pre1 #(map_post fm post1) #_ f
      (fun x -> map_pre_act #_ #_ #(x:am & (g (fm x) #ictx)._1) (fun y -> (| x, y |)) (g (fm x) #ictx)._3) |)

let frame
     (#a:Type u#a)
     (#r:reifiability)
     (#opens:inames)
     (#pre #post #frame:_)
     (f:act a r opens pre post)
: act a r opens (pre `star` frame) (fun x -> post x `star` frame)
= fun #ictx ->
  let (| am, fm, f |) = f #ictx in
  (| am, fm, frame_pre_act f |)

let lift_ghost_atomic
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens:inames)
    (f:act a Ghost opens pre post)
: act a Atomic opens pre post
= fun #ictx ->
  let (| am, fm, f |) = f #ictx in
  (| am, fm, lift_pre_act_ghost f |)

let weaken 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#r0 #r1:reifiability)
    (#opens opens':inames)
    (f:act a r0 opens pre post)
: act a (r0 ^^ r1) (Set.union opens opens') pre post
= if r0 = r1 then f
  else (
    match r0, r1 with
    | Atomic, Ghost -> f
    | _ -> lift_ghost_atomic #a #pre #post #opens f
  )

let sub_pre_act_atomic 
    (#a:Type)
    (#r:reifiability)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens:inames)
    (pre':slprop { slprop_equiv pre pre' })
    (post':a -> slprop { forall x. slprop_equiv (post x) (post' x) })
    (f:pre_act a r opens pre post)
: pre_act a r opens pre' post'
= I.slprop_equiv_elim pre pre';
  introduce forall x. post x == post' x
  with I.slprop_equiv_elim (post x) (post' x);
  f

let sub 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#r:_)
    (#opens:inames)
    (pre':slprop { slprop_equiv pre pre' })
    (post':a -> slprop { forall x. slprop_equiv (post x) (post' x) })
    (f:act a r opens pre post)
: act a r opens pre' post'
= fun #ictx ->
  let (| am, fm, f |) = f #ictx in
  (| am, fm, sub_pre_act_atomic _ _ f |)

let lift (#a:Type u#a) #r #opens #pre #post
         (m:act a r opens pre post)
: stt a pre post
= let (| a, f, m |) = m #emp_inames in
  bind (stt_of_action4 m) (fun x -> I.return (f x) post)

///////////////////////////////////////////////////////
// invariants
///////////////////////////////////////////////////////
let inv i p = inv i p
let dup_inv (i:iref) (p:slprop) =
  lift_pre_act0_act fun #ictx -> ITA.dup_inv ictx i p
let new_invariant p = lift_pre_act0_act fun #ictx -> ITA.new_invariant ictx p
let exists_equiv (#a:_) (#p:a -> slprop)
  : squash (op_exists_Star p == (exists* x. p x))
  = let pf = I.slprop_equiv_exists p (fun x -> p x) () in
    let pf = FStar.Squash.return_squash pf in
    I.slprop_equiv_elim (op_exists_Star p) (exists* x. p x)
 
let fresh_invariant ctx p = lift_pre_act0_act fun #ictx -> ITA.fresh_invariant ictx p ctx

let inames_live_inv (i:iref) (p:slprop) = lift_pre_act0_act fun #ictx -> ITA.inames_live_inv ictx i p

let with_invariant #a #r #fp #fp' #f_opens #p i f =
  fun #ictx ->
  let ictx' = Sep.add_inv ictx i in
  let (| af, mf, f |) = f () #ictx' in
  (| af, mf, ITA.with_invariant i f |)

let invariant_name_identifies_invariant p q i =
  lift_pre_act0_act
  fun #ictx -> 
    ITA.invariant_name_identifies_invariant ictx i p q


////////////////////////////////////////////////////////////////////////
// later and credits
////////////////////////////////////////////////////////////////////////
let later_intro (p:slprop)
: act unit Ghost emp_inames p (fun _ -> later p)
= lift_pre_act0_act fun #ictx -> ITA.later_intro ictx p

let later_elim (p:slprop)
: act unit Ghost emp_inames (later p ** later_credit 1) (fun _ -> p)
= lift_pre_act0_act fun #ictx -> ITA.later_elim ictx p

let implies_elim (p:slprop) (q:slprop { implies p q })
: act unit Ghost emp_inames p (fun _ -> q)
= lift_pre_act0_act fun #ictx -> ITA.implies_elim ictx p q

let buy1 ()
: stt unit emp (fun _ -> later_credit 1)
= stt_of_action0 (ITA.buy emp_inames)

///////////////////////////////////////////////////////////////////
// Core operations on references
///////////////////////////////////////////////////////////////////
let core_ref = Mem.core_ref
let core_ref_null = Mem.core_ref_null
let is_core_ref_null = Mem.core_ref_is_null
let pts_to #a #p r x = Sep.lift (Mem.pts_to #a #p r x)
let timeless_pts_to #a #p r x = Sep.timeless_lift (Mem.pts_to #a #p r x)
let pts_to_not_null #a #p r v =
  lift_pre_act0_act fun #ictx ->
  ITA.lift_mem_action (Mem.pts_to_not_null_action #a #p (Sep.lower_inames ictx) r v)

let lift_eqs ()
: squash (
  Sep.lift Mem.emp == emp /\
  (forall p. Sep.lift (Mem.pure p) == pure p) /\
  (forall p q. Sep.lift (Mem.star p q) == star (Sep.lift p) (Sep.lift q)))
= FStar.Classical.forall_intro Sep.lift_pure_eq;
  FStar.Classical.forall_intro_2 Sep.lift_star_eq;
  Sep.lift_emp_eq()

let alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: act (ref a pcm) Atomic emp_inames emp (fun r -> pts_to r x)
= lift_eqs(); lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action (Mem.alloc_action #a #pcm (Sep.lower_inames ictx) x)

let read
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
= lift_pre_act1_act fun #ictx -> 
    ITA.lift_mem_action (Mem.select_refine #a #p (Sep.lower_inames ictx) r x f)

let write
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
= lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action (Mem.upd_gen #a #p (Sep.lower_inames ictx) r x y f)

let share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit
      Ghost
      emp_inames
      (pts_to r (v0 `op pcm` v1))
      (fun _ -> pts_to r v0 `star` pts_to r v1)
= lift_eqs(); lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action (Mem.split_action #a #pcm (Sep.lower_inames ictx) r v0 v1)

let gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1))
      Ghost
      emp_inames
      (pts_to r v0 `star` pts_to r v1)
      (fun _ -> pts_to r (op pcm v0 v1))
= lift_eqs(); lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action (Mem.gather_action #a #pcm (Sep.lower_inames ictx) r v0 v1)

///////////////////////////////////////////////////////////////////
// big refs
///////////////////////////////////////////////////////////////////
let big_pts_to #a #pcm r x = Sep.lift (Mem.big_pts_to #a #pcm r x)
let timeless_big_pts_to #a #p r x = Sep.timeless_lift (Mem.big_pts_to #a #p r x)
let big_pts_to_not_null #a #p r v = lift_pre_act0_act fun #ictx ->
  ITA.lift_mem_action (Mem.big_pts_to_not_null_action #a #p (Sep.lower_inames ictx) r v)

let big_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: act (ref a pcm) Atomic emp_inames emp (fun r -> big_pts_to r x)
= lift_eqs(); lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action (Mem.big_alloc_action #a #pcm (Sep.lower_inames ictx) x)

let big_read
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
= lift_pre_act2_act fun #ictx ->
    lift_eqs();
    ITA.lift_mem_action (Mem.big_select_refine#a #p (Sep.lower_inames ictx) r x f)

let big_write
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
= lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action (Mem.big_upd_gen #a #p (Sep.lower_inames ictx) r x y f)

let big_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit
      Ghost
      emp_inames
      (big_pts_to r (v0 `op pcm` v1))
      (fun _ -> big_pts_to r v0 `star` big_pts_to r v1)
= lift_eqs(); lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action (Mem.big_split_action #a #pcm (Sep.lower_inames ictx) r v0 v1)

let big_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1))
      Ghost
      emp_inames
      (big_pts_to r v0 `star` big_pts_to r v1)
      (fun _ -> big_pts_to r (op pcm v0 v1))
= lift_eqs(); lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action (Mem.big_gather_action #a #pcm (Sep.lower_inames ictx) r v0 v1)

let nb_pts_to #a #pcm r x = Sep.lift <| Mem.nb_pts_to #a #pcm r x
let timeless_nb_pts_to #a #p r x = Sep.timeless_lift <| Mem.nb_pts_to #a #p r x
let nb_pts_to_not_null #a #p r v = lift_pre_act0_act fun #ictx ->
  ITA.lift_mem_action (Mem.nb_pts_to_not_null_action #a #p (Sep.lower_inames ictx) r v)

let nb_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: act (ref a pcm) Atomic emp_inames emp (fun r -> nb_pts_to r x)
= lift_eqs (); lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action (Mem.nb_alloc_action #a #pcm (Sep.lower_inames ictx) x)

let nb_read
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
= lift_pre_act3_act fun #ictx ->
    ITA.lift_mem_action (Mem.nb_select_refine #a #p (Sep.lower_inames ictx) r x f)

let nb_write
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
= lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action <| Mem.nb_upd_gen #a #p (Sep.lower_inames ictx) r x y f

let nb_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit
      Ghost
      emp_inames
      (nb_pts_to r (v0 `op pcm` v1))
      (fun _ -> nb_pts_to r v0 `star` nb_pts_to r v1)
= lift_eqs(); lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action <| Mem.nb_split_action #a #pcm (Sep.lower_inames ictx) r v0 v1

let nb_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1))
      Ghost
      emp_inames
      (nb_pts_to r v0 `star` nb_pts_to r v1)
      (fun _ -> nb_pts_to r (op pcm v0 v1))
= lift_eqs(); lift_pre_act0_act fun #ictx ->
    ITA.lift_mem_action <| Mem.nb_gather_action #a #pcm (Sep.lower_inames ictx) r v0 v1


///////////////////////////////////////////////////////////////////
// pure
///////////////////////////////////////////////////////////////////
let pure_true ()
= Mem.pure_true_emp ();
  slprop_equiv_elim (pure True) emp;
  calc (==) {
    pure True;
    (==) { lift_eqs () }
    Sep.lift (Mem.pure True);
    (==) {  Mem.pure_true_emp ();
            Mem.slprop_extensionality (Mem.pure True) Mem.emp }
    Sep.lift (Mem.emp);
    (==) { lift_eqs () }
    emp;
 };
 coerce_eq () <| slprop_equiv_refl (pure True)

let intro_pure (p:prop) (pf:squash p)
: act unit Ghost emp_inames emp (fun _ -> pure p)
= lift_pre_act0_act fun #ictx -> ITA.intro_pure #ictx p pf

let elim_pure (p:prop)
: act (squash p) Ghost emp_inames (pure p) (fun _ -> emp)
= lift_pre_act0_act fun #ictx -> ITA.elim_pure #ictx p

///////////////////////////////////////////////////////////////////
// exists*
///////////////////////////////////////////////////////////////////
module F = FStar.FunctionalExtensionality

let thunk (p:slprop) = fun (_:unit) -> p

let intro_exists' (#a:Type u#a) (p:a -> slprop) (x:erased a)
: act unit Ghost emp_inames (p x) (thunk (op_exists_Star p))
= lift_pre_act0_act fun #ictx -> ITA.intro_exists #ictx p x

let intro_exists'' (#a:Type u#a) (p:a -> slprop) (x:erased a)
: act unit Ghost emp_inames (p x) (thunk (exists* x. p x))
= exists_equiv #a #p; intro_exists' p x

let intro_exists (#a:Type u#a) (p:a -> slprop) (x:erased a)
: act unit Ghost emp_inames (p x) (fun _ -> exists* x. p x)
= intro_exists'' p x

let exists_ok_mem #a (p: a->slprop) = m:erased mem { interp (exists* x. p x) m }
let exists_get_witness #a (p: a->slprop) (m:exists_ok_mem p) : x:erased a { interp (p x) m } =
  exists_equiv #a #p;
  interp_exists p;
  IndefiniteDescription.indefinite_description_tot a (fun x -> interp (p x) m)

let elim_exists (#a:Type u#a) (p:a -> slprop)
: act (erased a) Ghost emp_inames (exists* x. p x) (fun x -> p x)
= fun #ictx ->
  let k: pre_act (exists_ok_mem p) Ghost ictx (exists* x. p x) (fun x -> p (exists_get_witness p x)) =
   fun frame m0 ->
    sep_laws();
    let m1, m2 = split_mem (exists* x. p x) (frame `Sep.star` mem_invariant ictx m0) (hide m0) in 
    assert FStar.Preorder.reflexive is_ghost_action;
    intro_star (p (exists_get_witness p m1)) (frame `Sep.star` mem_invariant ictx m0) m1 m2;
    m1, m0
  in (| exists_ok_mem p, exists_get_witness p, k |)

let drop p = lift_pre_act0_act fun #ictx -> ITA.drop #ictx p

let core_ghost_ref = Mem.core_ghost_ref
let ghost_pts_to #a #pcm r x = Sep.lift (Mem.ghost_pts_to #a #pcm r x)
let timeless_ghost_pts_to #a #p r x = Sep.timeless_lift (Mem.ghost_pts_to #a #p r x)
let ghost_alloc #a #pcm x = let open Mem in lift_eqs (); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| ghost_alloc #(Sep.lower_inames ictx) #a #pcm x
let ghost_read #a #p r x f = let open Mem in lift_eqs(); lift_pre_act1_act fun #ictx -> ITA.lift_mem_action <| ghost_read #(Sep.lower_inames ictx) #a #p r x f
let ghost_write #a #p r x y f = let open Mem in lift_eqs(); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| ghost_write #(Sep.lower_inames ictx) #a #p r x y f
let ghost_share #a #pcm r v0 v1 = let open Mem in lift_eqs(); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| ghost_share #(Sep.lower_inames ictx) #a #pcm r v0 v1
let ghost_gather #a #pcm r v0 v1 = let open Mem in lift_eqs(); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| ghost_gather #(Sep.lower_inames ictx) #a #pcm r v0 v1

let big_ghost_pts_to #a #p r x = Sep.lift (Mem.big_ghost_pts_to #a #p r x)
let timeless_big_ghost_pts_to #a #p r x = Sep.timeless_lift (Mem.big_ghost_pts_to #a #p r x)
let big_ghost_alloc #a #pcm x = let open Mem in lift_eqs(); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| big_ghost_alloc #(Sep.lower_inames ictx) #a #pcm x
let big_ghost_read #a #p r x f = let open Mem in lift_eqs(); lift_pre_act2_act fun #ictx -> ITA.lift_mem_action <| big_ghost_read #(Sep.lower_inames ictx) #a #p r x f
let big_ghost_write #a #p r x y f = let open Mem in lift_eqs(); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| big_ghost_write #(Sep.lower_inames ictx) #a #p r x y f
let big_ghost_share #a #pcm r v0 v1 = let open Mem in lift_eqs(); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| big_ghost_share #(Sep.lower_inames ictx) #a #pcm r v0 v1
let big_ghost_gather #a #pcm r v0 v1 = let open Mem in lift_eqs(); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| big_ghost_gather #(Sep.lower_inames ictx) #a #pcm r v0 v1

let nb_ghost_pts_to #a #p r x = Sep.lift (Mem.nb_ghost_pts_to #a #p r x)
let timeless_nb_ghost_pts_to #a #p r x = Sep.timeless_lift (Mem.nb_ghost_pts_to #a #p r x)
let nb_ghost_alloc #a #pcm x = let open Mem in lift_eqs(); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| nb_ghost_alloc #(Sep.lower_inames ictx) #a #pcm x
let nb_ghost_read #a #p r x f = let open Mem in lift_eqs(); lift_pre_act3_act fun #ictx -> ITA.lift_mem_action <| nb_ghost_read #(Sep.lower_inames ictx) #a #p r x f
let nb_ghost_write #a #p r x y f = let open Mem in lift_eqs(); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| nb_ghost_write #(Sep.lower_inames ictx) #a #p r x y f
let nb_ghost_share #a #pcm r v0 v1 = let open Mem in lift_eqs(); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| nb_ghost_share #(Sep.lower_inames ictx) #a #pcm r v0 v1
let nb_ghost_gather #a #pcm r v0 v1 = let open Mem in lift_eqs(); lift_pre_act0_act fun #ictx -> ITA.lift_mem_action <| nb_ghost_gather #(Sep.lower_inames ictx) #a #pcm r v0 v1


let lift_erased #a ni_a #opens #pre #post f =
  fun #ictx -> 
    (| erased (reveal f #ictx)._1, (fun x -> ni_a ((reveal f #ictx)._2 (reveal x))),
      ITA.lift_ghost #(erased (reveal f #ictx)._1) (fun x -> reveal x)
        (hide (map_pre_act hide (reveal f #ictx)._3)) |)

let equiv_refl a =
  lift_pre_act0_act fun #ictx -> ITA.equiv_refl #ictx a

let equiv_dup (a b:slprop) =
  lift_pre_act0_act fun #ictx -> ITA.equiv_dup #ictx a b

let equiv_trans (a b c:slprop) =
  lift_pre_act0_act fun #ictx -> ITA.equiv_trans #ictx a b c

let equiv_elim (a b:slprop) =
  lift_pre_act0_act fun #ictx -> ITA.equiv_elim #ictx a b

let slprop_ref = Sep.slprop_ref
let slprop_ref_pts_to = Sep.slprop_ref_pts_to
let slprop_ref_alloc y = lift_pre_act0_act fun #ictx -> ITA.slprop_ref_alloc #ictx y
let slprop_ref_share x y = lift_pre_act0_act fun #ictx -> ITA.slprop_ref_share #ictx x y
let slprop_ref_gather x y1 y2 = lift_pre_act0_act fun #ictx -> ITA.slprop_ref_gather #ictx x y1 y2