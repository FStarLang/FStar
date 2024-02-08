module PulseCore.Action
module Sem = PulseCore.Semantics
module Mem = PulseCore.Memory
module I = PulseCore.InstantiatedSemantics
module M = PulseCore.MonotonicStateMonad
module F = FStar.FunctionalExtensionality
friend PulseCore.InstantiatedSemantics
open FStar.PCM
open FStar.Ghost
open PulseCore.Memory
open PulseCore.InstantiatedSemantics

//////////////////////////////////////////////////////
// An abstraction on top of memory actions
//////////////////////////////////////////////////////

(* The type of atomic actions *)
let action
    (a:Type u#a)
    (except:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max a 2)
= frame:slprop ->
  Sem.mst_sep_aux state
    (inames_ok except)
    (state0 except).invariant
    a 
    (pre `star` frame)
    (fun x -> post x `star` frame)

let return_action
    (#a:Type u#a)
    (#except:inames)
    (#post:a -> slprop)
    (x:a)
: action a except (post x) post
= fun frame -> M.weaken (M.return x)

let bind_action
     (#a:Type u#a)
     (#b:Type u#b)
     (#except:inames)
     (#pre1 #post1 #post2:_)
     (f:action a except pre1 post1)
     (g:(x:a -> action b except (post1 x) post2))
: action b except pre1 post2
= fun frame -> M.weaken (M.bind (f frame) (fun x -> g x frame))

let frame_action
     (#a:Type u#a)
     (#except:inames)
     (#pre #post #frame:_)
     (f:action a except pre post)
: action a except (pre `star` frame) (fun x -> post x `star` frame)
= fun frame' -> f (frame `star` frame')

let stt_of_action (#a:Type u#100) #pre #post (m:action a Set.empty pre post)
: stt a pre post
= let step (frame:slprop)
    : Sem.mst_sep state a (pre `star` frame) (fun x -> post x `star` frame)
    = M.weaken (m frame)
  in
  let action : Sem.action state a = {pre=pre; post=F.on_dom _ post; step} in
  let m : Sem.m a pre _ = Sem.act action in
  fun _ -> m

let stt_of_action0 (#a:Type u#0) #pre #post (m:action a Set.empty pre post)
: stt a pre post
= let step (frame:slprop)
    : Sem.mst_sep state a (pre `star` frame) (fun x -> post x `star` frame)
    = M.weaken (m frame)
  in
  let action : Sem.action state a = {pre=pre; post=F.on_dom _ post; step} in
  fun _ -> Sem.act_as_m0 action
  
let stt_of_action1 (#a:Type u#1) #pre #post (m:action a Set.empty pre post)
: stt a pre post
= let step (frame:slprop)
    : Sem.mst_sep state a (pre `star` frame) (fun x -> post x `star` frame)
    = M.weaken (m frame)
  in
  let action : Sem.action state a = {pre=pre; post=F.on_dom _ post; step} in
  fun _ -> Sem.act_as_m1 u#2 u#100 action

let stt_of_action2 (#a:Type u#2) #pre #post (m:action a Set.empty pre post)
: stt a pre post
= let step (frame:slprop)
    : Sem.mst_sep state a (pre `star` frame) (fun x -> post x `star` frame)
    = M.weaken (m frame)
  in
  let action : Sem.action state a = {pre=pre; post=F.on_dom _ post; step} in
  fun _ -> Sem.act_as_m2 u#2 u#100 action
   
let mem_action_as_action
        (a:Type u#a)
        (except:inames)
        (req:slprop)
        (ens: a -> slprop)
        (act:Mem.action_except a except req ens)
: action a except req ens
= fun frame ->
    let thunk
      : unit -> MstTot a except req ens frame
      = fun _ -> act frame
    in
    M.of_msttotal _ _ _ _ thunk

let action_as_mem_action
        (a:Type u#a)
        (except:inames)
        (pre:slprop)
        (post: a -> slprop) 
        (act:action a except pre post)
: Mem.action_except a except pre post
= fun frame ->
    let m
      : M.mst state.evolves
                a 
                (fun s0 -> 
                    inames_ok except s0 /\
                    interp ((pre `star` locks_invariant except s0) `star` frame) s0)
                (fun s0 x s1 ->
                    inames_ok except s1 /\
                    interp ((post x `star` locks_invariant except s1) `star` frame) s1)
      = M.weaken (act frame)
    in
    M.to_msttotal _ _ _ _ m

//////////////////////////////////////////////////////
// Next, reversing the polarity of the inames index
//////////////////////////////////////////////////////

let iname = iname

let act 
    (a:Type u#a)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max a 2)
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

let weaken 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens opens':inames)
    (f:act a opens pre post)
: act a (Set.union opens opens') pre post
= f

let sub 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens:inames)
    (pre':slprop { slprop_equiv pre pre' })
    (post':a -> slprop { forall x. slprop_equiv (post x) (post' x) })
    (f:act a opens pre post)
: act a opens pre' post'
= I.slprop_equiv_elim pre pre';
  introduce forall x. post x == post' x
  with I.slprop_equiv_elim (post x) (post' x);
  f

let lift (#a:Type u#100) #opens #pre #post
         (m:act a opens pre post)
: stt a pre post
= stt_of_action (m #emp_inames)

let lift0 (#a:Type u#0) #opens #pre #post
          (m:act a opens pre post)
: stt a pre post
= stt_of_action0 (m #emp_inames)

let lift1 (#a:Type u#1) #opens #pre #post
          (m:act a opens pre post)
: stt a pre post
= stt_of_action1 (m #emp_inames)

let lift2 (#a:Type u#2) #opens #pre #post
          (m:act a opens pre post)
: stt a pre post
= stt_of_action2 (m #emp_inames)
///////////////////////////////////////////////////////
// invariants
///////////////////////////////////////////////////////

let inv = inv
let name_of_inv = name_of_inv

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
    let ictx' = Mem.add_inv ictx i in
    let f = action_as_mem_action _ _ _ _ (f () #ictx') in
    let m = with_invariant i f in
    mem_action_as_action _ _ _ _ m


///////////////////////////////////////////////////////////////////
// Core operations on references
///////////////////////////////////////////////////////////////////

let ref (a:Type u#a) (p:pcm a) = ref a p
let ref_null (#a:Type u#a) (p:pcm a) = core_ref_null
let is_ref_null (#a:Type u#a) (#p:pcm a) (r:ref a p) = core_ref_is_null r
let pts_to = pts_to
let pts_to_not_null #a #p r v =
    fun #ictx -> mem_action_as_action _ _ _ _ (pts_to_not_null_action ictx r v)

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

let witnessed = witnessed
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
let pure_true ()
= Mem.pure_true_emp ();
  slprop_equiv_elim (pure True) emp;
  coerce_eq () <| slprop_equiv_refl (pure True)

let intro_pure (p:prop) (pf:squash p)
: act unit emp_inames emp (fun _ -> pure p)
= fun #ictx -> mem_action_as_action _ _ _ _ (intro_pure #ictx p pf)

let elim_pure (p:prop)
: act (squash p) emp_inames (pure p) (fun _ -> emp)
= fun #ictx -> mem_action_as_action _ _ _ _ (elim_pure #ictx p)

///////////////////////////////////////////////////////////////////
// exists*
///////////////////////////////////////////////////////////////////
module F = FStar.FunctionalExtensionality
let exists_equiv (#a:_) (#p:a -> slprop)
  : squash (op_exists_Star p == (exists* x. p x))
  = let pf = I.slprop_equiv_exists p (fun x -> p x) () in
    let pf = FStar.Squash.return_squash pf in
    I.slprop_equiv_elim (op_exists_Star p) (exists* x. p x)

let thunk (p:slprop) = fun (_:unit) -> p

let intro_exists' (#a:Type u#a) (p:a -> slprop) (x:erased a)
: act unit emp_inames (p x) (thunk (op_exists_Star p))
= fun #ictx -> mem_action_as_action _ _ _ _ (intro_exists #ictx (F.on_dom a p) x)

let intro_exists'' (#a:Type u#a) (p:a -> slprop) (x:erased a)
: act unit emp_inames (p x) (thunk (exists* x. p x))
= coerce_eq (exists_equiv #a #p) (intro_exists' #a p x)

let intro_exists (#a:Type u#a) (p:a -> slprop) (x:erased a)
: act unit emp_inames (p x) (fun _ -> exists* x. p x)
= intro_exists'' p x

let elim_exists' (#a:Type u#a) (p:a -> slprop)
: act (erased a) emp_inames (op_exists_Star p) (fun x -> p x)
= fun #ictx -> mem_action_as_action _ _ _ _ (witness_h_exists #ictx (F.on_dom a p))

let elim_exists (#a:Type u#a) (p:a -> slprop)
: act (erased a) emp_inames (exists* x. p x) (fun x -> p x)
= coerce_eq (exists_equiv #a #p) (elim_exists' #a p)

let drop p
= fun #ictx -> mem_action_as_action _ _ _ _ (drop #ictx p)
