module PulseCore.Action
module Sem = PulseCore.Semantics
module Mem = PulseCore.Memory
module I = PulseCore.InstantiatedSemantics
module M = PulseCore.MonotonicStateMonad
module F = FStar.FunctionalExtensionality
module PST = PulseCore.PreorderStateMonad
friend PulseCore.InstantiatedSemantics
open FStar.PCM
open FStar.Ghost
open PulseCore.Memory
open PulseCore.InstantiatedSemantics

//////////////////////////////////////////////////////
// An abstraction on top of memory actions
//////////////////////////////////////////////////////

(* The type of semantic actions, does not distinguish reifiability *)
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

let iname = iname

let maybe_ghost (r:reifiability { r =!= UsesInvariants}) =
  match r with
  | Ghost -> true
  | _ -> false

let pre_act
    (a:Type u#a)
    (r:reifiability)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
= match r with
  | UsesInvariants ->
    Mem.action_except a opens pre post
  | _ ->
    Mem._pst_action_except a (maybe_ghost r) opens pre post

let force 
    #a (#r:reifiability { r =!= UsesInvariants})
    (#opens:inames) (#pre:slprop) (#post:a -> slprop)    
    (f:pre_act a r opens pre post)
: Mem._pst_action_except a (maybe_ghost r) opens pre post
= f

let mem_action_as_action
        (#a:Type u#a)
        (#except:inames)
        (#req:slprop)
        (#ens: a -> slprop)
        (act:Mem.action_except a except req ens)
: action a except req ens
= fun frame ->
    let thunk
      : unit -> MstTot a except req ens frame
      = fun _ -> act frame
    in
    M.of_msttotal _ _ _ _ thunk

let mem_pst_action_as_action
        (#a:Type u#a)
        (#except:inames)
        (#req:slprop)
        (#ens: a -> slprop)
        (act:Mem.pst_action_except a except req ens)
: action a except req ens
= fun frame -> M.weaken <| M.lift_pst (act frame)

let action_of_pre_act
    (#a:Type u#a)
    (#r:reifiability)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (f:pre_act a r opens pre post)
: action a opens pre post
= match r with
  | UsesInvariants -> mem_action_as_action f
  | _ -> mem_pst_action_as_action f

let act 
    (a:Type u#a)
    (r:reifiability)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max a 2)
= #ictx:inames_disj opens ->
   pre_act a r ictx pre post
  
let return_pre_act
    (#a:Type u#a)
    (#except:inames)
    (#post:a -> slprop)
    (x:a)
: pre_act a Ghost except (post x) post
= Mem.ghost_action_preorder ();
  fun frame m0 -> x, m0

let bind_pre_act_ghost
     (#a:Type u#a)
     (#b:Type u#b)
     (#except:inames)
     (#pre1 #post1 #post2:_)
     (f:pre_act a Ghost except pre1 post1)
     (g:(x:a -> pre_act b Ghost except (post1 x) post2))
: pre_act b Ghost except pre1 post2
= Mem.ghost_action_preorder ();
  fun frame ->
    PST.weaken (PST.bind (f frame) (fun x -> g x frame))

let bind_pre_act_reifiable
     (#a:Type u#a)
     (#b:Type u#b)
     (#except:inames)
     (#pre1 #post1 #post2:_)
     (f:pre_act a Reifiable except pre1 post1)
     (g:(x:a -> pre_act b Reifiable except (post1 x) post2))
: pre_act b Reifiable except pre1 post2
= fun frame ->
    PST.weaken (PST.bind (f frame) (fun x -> g x frame))

let bind_pre_act_non_reifiable
     (#a:Type u#a)
     (#b:Type u#b)
     (#except:inames)
     (#pre1 #post1 #post2:_)
     ($f:pre_act a UsesInvariants except pre1 post1)
     ($g:(x:a -> pre_act b UsesInvariants except (post1 x) post2))
: pre_act b UsesInvariants except pre1 post2
= fun frame ->
    let x = f frame in
    g x frame

let bind_pre_act
     (#a:Type u#a)
     (#b:Type u#b)
     (#r:reifiability)
     (#except:inames)
     (#pre1 #post1 #post2:_)
     (f:pre_act a r except pre1 post1)
     (g:(x:a -> pre_act b r except (post1 x) post2))
: pre_act b r except pre1 post2
= match r with
  | Ghost -> 
    bind_pre_act_ghost #a #b #except #pre1 #post1 #post2 f g
  | Reifiable ->
    bind_pre_act_reifiable #a #b #except #pre1 #post1 #post2 f g
  | UsesInvariants ->
    bind_pre_act_non_reifiable #a #b #except #pre1 #post1 #post2 f g

let frame_pre_act_ghost
     (#a:Type u#a)
     (#except:inames)
     (#pre #post #frame:_)
     (f:pre_act a Ghost except pre post)
: pre_act a Ghost except (pre `star` frame) (fun x -> post x `star` frame)
= fun frame' -> f (frame `star` frame')

let frame_pre_act_reifiable
     (#a:Type u#a)
     (#except:inames)
     (#pre #post #frame:_)
     (f:pre_act a Reifiable except pre post)
: pre_act a Reifiable except (pre `star` frame) (fun x -> post x `star` frame)
= fun frame' -> f (frame `star` frame')

let frame_pre_act_non_reifiable
     (#a:Type u#a)
     (#except:inames)
     (#pre #post #frame:_)
     (f:pre_act a UsesInvariants except pre post)
: pre_act a UsesInvariants except (pre `star` frame) (fun x -> post x `star` frame)
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
  | Reifiable -> frame_pre_act_reifiable #a #except #pre #post #frame f
  | _ -> frame_pre_act_non_reifiable #a #except #pre #post #frame f

let lift_pre_act_ghost
     (#a:Type u#a)
     (#except:inames)
     (#pre #post:_)
     (f:pre_act a Ghost except pre post)
: pre_act a Reifiable except pre post
= f

let lift_pre_act_reifiablity
     (#a:Type u#a)
     (#r:_)
     (#except:inames)
     (#pre #post:_)
     (f:pre_act a r except pre post)
: pre_act a UsesInvariants except pre post
= if r = UsesInvariants then f
  else let f : pre_act a Reifiable except pre post = f in
       fun frame -> M.to_msttotal _ _ _ _ (M.lift_pst (f frame))

//////////////////////////////////////////////////////
// Next, reversing the polarity of the inames index
//////////////////////////////////////////////////////

let return 
    (#a:Type u#a)
    (#r:reifiability)
    (#post:a -> slprop)
    (x:a)
: act a r emp_inames (post x) post
= fun #ictx ->
    let m = return_pre_act #a #ictx #post x in
    match r with
    | Ghost -> m
    | Reifiable -> m
    | _ -> lift_pre_act_reifiablity m

let bind
     (#a:Type u#a)
     (#b:Type u#b)
     (#r:reifiability)
     (#opens:inames)
     (#pre1 #post1 #post2:_)
     (f:act a r opens pre1 post1)
     (g:(x:a -> act b r opens (post1 x) post2))
: act b r opens pre1 post2
= fun #ictx -> bind_pre_act #a #b #r #ictx #pre1 #post1 #post2 (f #ictx) (fun x -> g x #ictx)

let frame
     (#a:Type u#a)
     (#r:reifiability)
     (#opens:inames)
     (#pre #post #frame:_)
     (f:act a r opens pre post)
: act a r opens (pre `star` frame) (fun x -> post x `star` frame)
= fun #ictx -> frame_pre_act (f #ictx)

let lift_ghost_reifiable
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens:inames)
    (f:act a Ghost opens pre post)
: act a Reifiable opens pre post
= fun #ictx -> lift_pre_act_ghost (f #ictx)

let lift_reifiability 
    (#a:Type)
    (#r:_)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens:inames)
    (f:act a r opens pre post)
: act a UsesInvariants opens pre post
= fun #ictx -> lift_pre_act_reifiablity (f #ictx)

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
    | UsesInvariants, _ -> f
    | _, UsesInvariants -> lift_reifiability f
    | Reifiable, Ghost -> f
    | Ghost, Reifiable -> lift_ghost_reifiable #a #pre #post #opens f
  )

let sub_pre_act_reifiable 
    (#a:Type)
    (#r:reifiability { r =!= UsesInvariants})
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

let sub_pre_act_non_reifiable 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens:inames)
    (pre':slprop { slprop_equiv pre pre' })
    (post':a -> slprop { forall x. slprop_equiv (post x) (post' x) })
    (f:pre_act a UsesInvariants opens pre post)
: pre_act a UsesInvariants opens pre' post'
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
= match r with
  | UsesInvariants ->
    fun #ictx -> sub_pre_act_non_reifiable #a #pre #post #ictx pre' post' (f #ictx)
  | _ ->
    fun #ictx -> sub_pre_act_reifiable #a #r #pre #post #ictx pre' post' (f #ictx)

let action_of_act 
    (#a:Type)
    (#r:reifiability)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (f:act a r opens pre post)
: action a emp_inames pre post
= action_of_pre_act (f #emp_inames)

let lift (#a:Type u#100) #r #opens #pre #post
         (m:act a r opens pre post)
: stt a pre post
= stt_of_action (action_of_act m)

let lift0 (#a:Type u#0) #r #opens #pre #post
          (m:act a r opens pre post)
: stt a pre post
= stt_of_action0 (action_of_act m)

let lift1 (#a:Type u#1) #r #opens #pre #post
          (m:act a r opens pre post)
: stt a pre post
= stt_of_action1 (action_of_act m)

let lift2 (#a:Type u#2) #r #opens #pre #post
          (m:act a r opens pre post)
: stt a pre post
= stt_of_action2 (action_of_act m)
///////////////////////////////////////////////////////
// invariants
///////////////////////////////////////////////////////

let inv = inv
let allocated_name = pre_inv
let allocated_name_of_inv = pre_inv_of_inv
let name_of_allocated_name = name_of_pre_inv

let new_invariant (p:slprop)
: act (inv p) UsesInvariants emp_inames p (fun _ -> emp)
= fun #ictx -> new_invariant ictx p

let fresh_invariant ctx p
: act (i:inv p { fresh_wrt (name_of_inv i) ctx  })
      UsesInvariants emp_inames p (fun _ -> emp)
= fun #ictx -> fresh_invariant ictx p ctx

let with_invariant
    (#a:Type)
    (#r:_)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:inv p{not (mem_inv f_opens i)})
    (f:unit -> act a r f_opens (p `star` fp) (fun x -> p `star` fp' x))
: act a UsesInvariants (add_inv f_opens i) fp fp'
= fun #ictx ->
    let f : act a UsesInvariants f_opens (p `star` fp) (fun x -> p `star` fp' x)
      = match r with
        | UsesInvariants -> f ()
        | _ -> lift_reifiability (f ())
    in
    let ictx' = Mem.add_inv ictx i in
    with_invariant #a #fp #fp' #ictx i (f #ictx')

let distinct_invariants_have_distinct_names
    #p #q i j pf
= fun #ictx -> distinct_invariants_have_distinct_names ictx p q i j

let invariant_name_identifies_invariant
      (p q:slprop)
      (i:inv p)
      (j:inv q { name_of_inv i == name_of_inv j } )
= fun #ictx -> invariant_name_identifies_invariant ictx p q i j

///////////////////////////////////////////////////////////////////
// Core operations on references
///////////////////////////////////////////////////////////////////

let ref (a:Type u#a) (p:pcm a) = ref a p
let ref_null (#a:Type u#a) (p:pcm a) = core_ref_null
let is_ref_null (#a:Type u#a) (#p:pcm a) (r:ref a p) = core_ref_is_null r
let pts_to = Mem.pts_to
let pts_to_not_null #a #p r v #ictx = pts_to_not_null_action ictx r v

let alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:a{compatible pcm x x /\ pcm.refine x})
: act (ref a pcm) Reifiable emp_inames emp (fun r -> pts_to r x)
= fun #ictx -> alloc_action ictx x

let read
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (v:a{compatible p x v /\ p.refine v})
      Reifiable
      emp_inames
      (pts_to r x)
      (fun v -> pts_to r (f v))
= fun #ictx -> select_refine ictx r x f

let write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit
      Reifiable 
      emp_inames
      (pts_to r x)
      (fun _ -> pts_to r y)
= fun #ictx -> upd_gen ictx r x y f

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
= fun #ictx -> split_action ictx r v0 v1

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
= fun #ictx -> gather_action ictx r v0 v1

let witnessed = witnessed
let witness
    (#a:Type)
    (#pcm:pcm a)
    (r:erased (ref a pcm))
    (fact:stable_property pcm)
    (v:Ghost.erased a)
    (pf:squash (forall z. compatible pcm v z ==> fact z))
: act (witnessed r fact)
      UsesInvariants
      emp_inames
      (pts_to r v)
      (fun _ -> pts_to r v)
= fun #ictx -> witness ictx r fact v pf

let recall
    (#a:Type u#1)
    (#pcm:pcm a)
    (#fact:property a)
    (r:erased (ref a pcm))
    (v:Ghost.erased a)
    (w:witnessed r fact)
: act (v1:Ghost.erased a{compatible pcm v v1})
      UsesInvariants
      emp_inames
      (pts_to r v)
      (fun v1 -> pts_to r v `star` pure (fact v1))
= fun #ictx -> recall ictx r v w

///////////////////////////////////////////////////////////////////
// pure
///////////////////////////////////////////////////////////////////
let pure_true ()
= Mem.pure_true_emp ();
  slprop_equiv_elim (pure True) emp;
  coerce_eq () <| slprop_equiv_refl (pure True)

let intro_pure (p:prop) (pf:squash p)
: act unit Ghost emp_inames emp (fun _ -> pure p)
= fun #ictx -> intro_pure #ictx p pf

let elim_pure (p:prop)
: act (squash p) Ghost emp_inames (pure p) (fun _ -> emp)
= fun #ictx -> elim_pure #ictx p

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
: act unit Ghost emp_inames (p x) (thunk (op_exists_Star p))
= fun #ictx -> intro_exists #ictx (F.on_dom a p) x

let intro_exists'' (#a:Type u#a) (p:a -> slprop) (x:erased a)
: act unit Ghost emp_inames (p x) (thunk (exists* x. p x))
= coerce_eq (exists_equiv #a #p) (intro_exists' #a p x)

let intro_exists (#a:Type u#a) (p:a -> slprop) (x:erased a)
: act unit Ghost emp_inames (p x) (fun _ -> exists* x. p x)
= intro_exists'' p x

let elim_exists' (#a:Type u#a) (p:a -> slprop)
: act (erased a) Ghost emp_inames (op_exists_Star p) (fun x -> p x)
= fun #ictx -> witness_h_exists #ictx (F.on_dom a p)

let elim_exists (#a:Type u#a) (p:a -> slprop)
: act (erased a) Ghost emp_inames (exists* x. p x) (fun x -> p x)
= coerce_eq (exists_equiv #a #p) (elim_exists' #a p)

let drop p = fun #ictx -> drop #ictx p

let ghost_ref = Mem.ghost_ref
let ghost_pts_to = Mem.ghost_pts_to
let ghost_alloc #a #pcm x = fun #ictx -> ghost_alloc #ictx #a #pcm x
let ghost_read #a #p r x f = fun #ictx -> ghost_read #ictx #a #p r x f
let ghost_write #a #p r x y f = fun #ictx -> ghost_write #ictx #a #p r x y f
let ghost_share #a #pcm r v0 v1 = fun #ictx -> ghost_share #ictx #a #pcm r v0 v1
let ghost_gather #a #pcm r v0 v1 = fun #ictx -> ghost_gather #ictx #a #pcm r v0 v1
let lift_erased #a ni_a #opens #pre #post f =
  fun #ictx ->
    let f : erased (pre_act a Ghost ictx pre post) =
      hide (reveal f #ictx)
    in
    lift_ghost #a #ictx #pre #post ni_a f