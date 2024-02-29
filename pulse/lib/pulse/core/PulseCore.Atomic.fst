module PulseCore.Atomic
module I = PulseCore.InstantiatedSemantics
module A = PulseCore.Action
open PulseCore.InstantiatedSemantics
open PulseCore.Action

let r_of_obs = function
  | Neutral -> Ghost
  | _ -> UsesInvariants

let stt_atomic a #obs opens pre post =
  A.act a (r_of_obs obs) opens pre post

let pure_equiv (p q:prop) (_:squash (p <==> q))
  : slprop_equiv (pure p) (pure q)
  = FStar.PropositionalExtensionality.apply p q;
    slprop_equiv_refl (pure p)

let equiv (#p #q:slprop) (pf:slprop_equiv p q)
: squash (p == q)
= let _ : squash (slprop_equiv p q) = FStar.Squash.return_squash pf in
  I.slprop_equiv_elim p q

let pure_trivial (p:prop) (_:squash p)
  : squash (pure p == emp)
  = calc (==) {
      pure p;
    (==) { equiv (pure_equiv p True ()) }
      pure True;
    (==) { equiv (A.pure_true ()) }
      emp;
  }

let emp_unit_r (p:slprop)
: squash (p ** emp == p)
= calc (==) {
    (p ** emp);
   (==) { equiv (slprop_equiv_comm p emp) }
    (emp ** p);
   (==) { equiv (slprop_equiv_unit p) }
     p;
  }

let return_eq' #a #r x post
: act a r emp_inames
      (post x ** pure (x == x))
      (fun r -> post r ** pure (r == x))
= A.return #a #_ #(fun r -> post r ** pure (r == x)) x

let return_eq 
    (#a:Type u#a)
    (#r:_)
    (#post:a -> slprop)
    (x:a)
: act a r emp_inames (post x) (fun r -> post r ** pure (r == x))
= emp_unit_r (post x);
  pure_trivial (x == x) ();
  coerce_eq () (return_eq' #a #r x post)

let return_atomic #a x post
: stt_atomic a #Neutral emp_inames
      (post x)
      (fun r -> post r ** pure (r == x))
= return_eq x

let return_atomic_noeq #a x post = A.return #a #_ #post x

let bind_atomic
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
= match r_of_obs obs1, r_of_obs obs2 with
  | Ghost, Ghost ->
    let e1 : act a Ghost opens pre1 post1 = e1 in
    let e2 : x:a -> act b Ghost opens (post1 x) post2 = e2 in
    A.bind e1 e2
  | _ ->
    let e1 : act a UsesInvariants opens pre1 post1 = A.lift_reifiability e1 in
    let e2 : x:a -> act b UsesInvariants opens (post1 x) post2 = 
        fun x -> lift_reifiability (e2 x) in
    A.bind e1 e2

let lift_observability
    (#a:Type u#a)
    (#obs #obs':_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
= if obs = obs' then e
  else A.lift_reifiability e

let lift_atomic0
    (#a:Type u#0)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
: stt a pre post
= A.lift0 e

let lift_atomic1
    (#a:Type u#1)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
: stt a pre post
= A.lift1 e

let lift_atomic2
    (#a:Type u#2)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
: stt a pre post
= A.lift2 e

let frame_atomic
    (#a:Type u#a)
    (#obs: observability)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (frame:slprop)
    (e:stt_atomic a #obs opens pre post)
: stt_atomic a #obs opens (pre ** frame) (fun x -> post x ** frame)
= A.frame e

let sub_atomic
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
= A.sub pre2 post2 e

let sub_invs_stt_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens1 #opens2:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens1 pre post)
    (_ : squash (inames_subset opens1 opens2))
: stt_atomic a #obs opens2 pre post
= assert (Set.equal (Set.union opens1 opens2) opens2);
  A.weaken #_ #_ #_ #_ #(r_of_obs obs) opens2 e

let stt_ghost a pre post = Ghost.erased (act a Ghost emp_inames pre post)
let return_ghost #a x p = Ghost.hide (return_eq x)
let return_ghost_noeq #a x p = Ghost.hide (A.return #_ #_ #p x)
let bind_ghost
    (#a:Type u#a)
    (#b:Type u#b)
    (#pre1:slprop)
    (#post1:a -> slprop)
    (#post2:b -> slprop)
    (e1:stt_ghost a pre1 post1)
    (e2:(x:a -> stt_ghost b (post1 x) post2))
: stt_ghost b  pre1 post2
= let e1 = Ghost.reveal e1 in
  let e2 = FStar.Ghost.Pull.pull (fun (x:a) -> Ghost.reveal (e2 x)) in
  Ghost.hide (A.bind e1 e2)

let lift_ghost_neutral
    (#a:Type u#a)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_ghost a pre post)
    (reveal_a:non_informative_witness a)
: stt_atomic a #Neutral emp_inames pre post
= Action.lift_erased reveal_a e

let lift_neutral_ghost
    (#a:Type u#a)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #Neutral emp_inames pre post)
: stt_ghost a pre post
= Ghost.hide e

let frame_ghost
    (#a:Type u#a)
    (#pre:slprop)
    (#post:a -> slprop)
    (frame:slprop)
    (e:stt_ghost a pre post)
: stt_ghost a (pre ** frame) (fun x -> post x ** frame)
= Ghost.hide (A.frame (Ghost.reveal e))
 
let sub_ghost pre2 post2 pf1 pf2 e
= Ghost.hide (A.sub pre2 post2 e)

let noop (p:slprop)
: stt_ghost unit p (fun _ -> p)
= Ghost.hide (A.return #_ #_ #(fun _ -> p) ())

let intro_pure (p:prop) (pf:squash p)
: stt_ghost unit emp (fun _ -> pure p)
= Ghost.hide (A.intro_pure p pf)

let elim_pure (p:prop)
: stt_ghost (squash p) (pure p) (fun _ -> emp)
= Ghost.hide (A.elim_pure p)

let intro_exists (#a:Type u#a) (p:a -> slprop) (x:erased a)
: stt_ghost unit (p x) (fun _ -> exists* x. p x)
= Ghost.hide (A.intro_exists p x)

let elim_exists (#a:Type u#a) (p:a -> slprop)
: stt_ghost (erased a) (exists* x. p x) (fun x -> p x)
= Ghost.hide (A.elim_exists p)

let ghost_reveal (a:Type) (x:erased a)
: stt_ghost a emp (fun y -> pure (reveal x == y))
= let m
    : stt_ghost a
        (pure (reveal x == reveal x))
        (fun y -> pure (reveal x == y))
    = Ghost.hide (A.return #_ #_ #(fun y -> pure (reveal x == y)) (reveal x))
  in
  pure_trivial (reveal x == reveal x) ();
  m

let new_invariant
    (p:slprop)
: stt_atomic (inv p) #Unobservable emp_inames p (fun _ -> emp)
= A.new_invariant p

let fresh_invariant = A.fresh_invariant

let with_invariant
    (#a:Type)
    (#obs:_)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:inv p{not (mem_inv f_opens i)})
    ($f:unit -> stt_atomic a #obs f_opens
                            (p ** fp)
                            (fun x -> p ** fp' x))
: stt_atomic a #(join_obs obs Unobservable) (add_inv f_opens i) fp fp'
= A.with_invariant i f

let distinct_invariants_have_distinct_names = A.distinct_invariants_have_distinct_names
let invariant_name_identifies_invariant = A.invariant_name_identifies_invariant

let pts_to_not_null #a #p r v = Ghost.hide (A.pts_to_not_null #a #p r v)
let alloc #a #pcm x = A.lift_reifiability (A.alloc x)
let read r x f = A.lift_reifiability (A.read r x f)
let write r x y f = A.lift_reifiability (A.write r x y f)
let share #a #pcm r v0 v1 = Ghost.hide (A.share r v0 v1)
let gather #a #pcm r v0 v1 = Ghost.hide (A.gather r v0 v1)
let witness #a #pcm r f v pf = A.witness r f v pf
let recall #a #pcm #fact r v w = A.recall r v w

let ghost_ref = A.ghost_ref
let ghost_pts_to = A.ghost_pts_to
let hide_ghost #a #pre #post 
              (f:stt_ghost a pre post)
: stt_ghost (erased a) pre (fun x -> post (reveal x))
= let f = Ghost.reveal f in
  Ghost.hide <|
  A.bind f
  (fun (r:a) ->
    A.return #(erased a) #_ #(fun (x:erased a) -> post (reveal x))
       (hide r))

let ghost_alloc #a #pcm x = Ghost.hide <| A.ghost_alloc #a #pcm x
let ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt_ghost (erased (v:a{compatible p x v /\ p.refine v}))
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))
= Ghost.hide <| A.ghost_read r x f

let ghost_write r x y f = Ghost.hide (A.ghost_write r x y f)
let ghost_share r v0 v1 = Ghost.hide (A.ghost_share r v0 v1)
let ghost_gather r v0 v1 = Ghost.hide (A.ghost_gather r v0 v1) 
let drop p = Ghost.hide (A.drop p)