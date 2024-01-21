module PulseCore.Action
module Sem = PulseCore.Semantics2
module Mem = PulseCore.Memory
module I = PulseCore.InstantiatedSemantics
open Mem
open I

let inames = Ghost.erased (FStar.Set.set iname)
let emp_inames : inames = Ghost.hide Set.empty

let join_inames (is1 is2 : inames) : inames =
  Set.union is1 is2

let inames_subset (is1 is2 : inames) : Type0 =
  Set.subset is1 is2

let (/!) (is1 is2 : inames) : Type0 =
  Set.disjoint is1 is2

unfold
let inames_disj (ictx:inames) : Type = is:inames{is /! ictx}

let act 
    (a:Type u#a)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
= #ictx:inames_disj opens ->
   action a ictx pre post

let return 
    (#a:Type u#a)
    (#post:a -> slprop)
    (x:a)
: act a emp_inames (post x) post
= fun #ictx -> return_action #a #ictx #post x

let bind
     (#a:Type u#a)
     (#b:Type u#b)
     (#opens:inames)
     (#pre1 #post1 #post2:_)
     (f:act a opens pre1 post1)
     (g:(x:a -> act b opens (post1 x) post2))
: act b opens pre1 post2
= fun #ictx -> bind_action #a #b #ictx #pre1 #post1 #post2 (f #ictx) (fun x -> g x #ictx)

let frame
     (#a:Type u#a)
     (#opens:inames)
     (#pre #post #frame:_)
     (f:act a opens pre post)
: act a opens (pre `star` frame) (fun x -> post x `star` frame)
= fun #ictx -> frame_action (f #ictx)

let lift (#a:Type u#2) #opens #pre #post
         (m:act a opens pre post)
: stt a pre post
= stt_of_action (m #emp_inames)

let new_invariant (p:slprop)
: act (inv p) emp_inames p (fun _ -> emp)
= fun #ictx -> 
    mem_action_as_action _ _ _ _ (new_invariant ictx p)

let with_invariant
    (#a:Type)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:inv p{not (mem_inv f_opens i)})
    (f:unit -> act a f_opens (p `star` fp) (fun x -> p `star` fp' x))
: act a (add_inv f_opens i) fp fp'
= fun #ictx ->
    let ictx' = add_inv ictx i in
    let f = action_as_mem_action _ _ _ _ (f () #ictx') in
    let m = with_invariant i f in
    mem_action_as_action _ _ _ _ m

let weaken 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens opens':inames)
    (f:act a opens pre post)
: act a (Set.union opens opens') pre post
= f

///////////////////////////////////////////////////////////////////
// Core operations on references
///////////////////////////////////////////////////////////////////
open FStar.PCM
open FStar.Ghost

let ref (a:Type u#a) (p:pcm a) = ref a p

let alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:a{compatible pcm x x /\ pcm.refine x})
: act (ref a pcm) emp_inames emp (fun r -> pts_to r x)
= fun #ictx ->
    mem_action_as_action _ _ _ _
        (alloc_action ictx x)

let read
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (v:a{compatible p x v /\ p.refine v}) emp_inames
      (pts_to r x)
      (fun v -> pts_to r (f v))
= fun #ictx ->
    mem_action_as_action _ _ _ _ (select_refine ictx r x f)

let write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit emp_inames
                  (pts_to r x)
                  (fun _ -> pts_to r y)
= fun #ictx -> mem_action_as_action _ _ _ _ (upd_gen ictx r x y f)

let share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit emp_inames
      (pts_to r (v0 `op pcm` v1))
      (fun _ -> pts_to r v0 `star` pts_to r v1)
= fun #ictx -> mem_action_as_action _ _ _ _ (split_action ictx r v0 v1)

let gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1))
    emp_inames
    (pts_to r v0 `star` pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))
= fun #ictx -> mem_action_as_action _ _ _ _ (gather_action ictx r v0 v1)

let witness
    (#a:Type)
    (#pcm:pcm a)
    (r:erased (ref a pcm))
    (fact:stable_property pcm)
    (v:Ghost.erased a)
    (pf:squash (forall z. compatible pcm v z ==> fact z))
: act (witnessed r fact) emp_inames (pts_to r v) (fun _ -> pts_to r v)
= fun #ictx -> mem_action_as_action _ _ _ _ (witness ictx r fact v pf)

let recall
    (#a:Type u#1)
    (#pcm:pcm a)
    (#fact:property a)
    (r:erased (ref a pcm))
    (v:Ghost.erased a)
    (w:witnessed r fact)
: act (v1:Ghost.erased a{compatible pcm v v1})
    emp_inames
    (pts_to r v)
    (fun v1 -> pts_to r v `star` pure (fact v1))
= fun #ictx -> mem_action_as_action _ _ _ _ (recall ictx r v w)

///////////////////////////////////////////////////////////////////
// pure
///////////////////////////////////////////////////////////////////
let intro_pure (p:prop) (pf:squash p)
: act unit emp_inames emp (fun _ -> pure p)
= fun #ictx -> mem_action_as_action _ _ _ _ (intro_pure #ictx p pf)

let elim_pure (p:prop)
: act (squash p) emp_inames (pure p) (fun _ -> emp)
= fun #ictx -> mem_action_as_action _ _ _ _ (elim_pure #ictx p)

///////////////////////////////////////////////////////////////////
// exists*
///////////////////////////////////////////////////////////////////
