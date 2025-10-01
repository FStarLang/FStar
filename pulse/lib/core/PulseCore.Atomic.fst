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

module A = PulseCore.Action
module I = PulseCore.InstantiatedSemantics
module Set = FStar.GhostSet
open PulseCore.InstantiatedSemantics
open PulseCore.Action

let r_of_obs = function
  | Neutral -> Ghost
  | _ -> Atomic

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
= A.return x

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

let return_atomic_noeq #a x post = A.return #a #_ #_ #post x

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
  | Ghost, Ghost -> A.bind_ghost e1 e2
  | Ghost, _ -> A.bind_atomic e1 e2
  | _, Ghost -> A.bind_atomic e1 e2

let lift_observability
    (#a:Type u#a)
    (#obs #obs':_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
= match r_of_obs obs, r_of_obs obs' with
  | Ghost, Atomic -> A.lift_ghost_atomic e
  | _ -> e

let lift_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
: stt a pre post
= A.lift e

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

let stt_ghost a opens pre post =
  Ghost.erased (act (erased a) Ghost opens pre (as_ghost_post post))

let lift_ghost_neutral'
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_ghost a opens pre post)
: stt_atomic (erased a) #Neutral opens pre (as_ghost_post post)
= A.lift_erased (fun (x: erased (erased a)) -> reveal x) e

let lift_ghost_neutral
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_ghost a opens pre post)
    (reveal_a:non_informative_witness a)
: stt_atomic a #Neutral opens pre post
= A.bind_ghost (lift_ghost_neutral' e) (fun x -> return #_ #_ #_ #post (reveal_a x))

let lift_neutral_ghost
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #Neutral opens pre post)
: stt_ghost a opens pre post
= A.bind_ghost e fun x -> A.return #_ #_ #_ #(as_ghost_post post) (hide x)

let return_ghost #a x p = lift_neutral_ghost (return_eq x)
let return_ghost_noeq #a x p = lift_neutral_ghost (A.return x)

let bind_ghost
    (#a:Type u#a)
    (#b:Type u#b)
    (#opens:inames)
    (#pre1:slprop)
    (#post1:a -> slprop)
    (#post2:b -> slprop)
    (e1:stt_ghost a opens pre1 post1)
    (e2:(x:a -> stt_ghost b opens (post1 x) post2))
: stt_ghost b opens pre1 post2
= A.bind_ghost e1 fun x -> lift_ghost_neutral' (e2 x)

let frame_ghost
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (frame:slprop)
    (e:stt_ghost a opens pre post)
: stt_ghost a opens (pre ** frame) (fun x -> post x ** frame)
= Ghost.hide (A.frame (Ghost.reveal e))
 
let sub_ghost pre2 post2 pf1 pf2 e
= Ghost.hide (A.sub pre2 (as_ghost_post post2) e)

let sub_invs_stt_ghost
    (#a:Type u#a)
    (#opens1 #opens2:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_ghost a opens1 pre post)
    (_ : squash (inames_subset opens1 opens2))
: stt_ghost a opens2 pre post
= assert (Set.equal (Set.union opens1 opens2) opens2);
  Ghost.hide (A.weaken #_ #_ #_ #_ #Ghost opens2 e)

let noop (p:slprop)
: stt_ghost unit emp_inames p (fun _ -> p)
= lift_neutral_ghost (A.return ())

let intro_pure (p:prop) (pf:squash p)
: stt_ghost unit emp_inames emp (fun _ -> pure p)
= lift_neutral_ghost (A.intro_pure p pf)

let elim_pure (p:prop)
: stt_ghost (squash p) emp_inames (pure p) (fun _ -> emp)
= lift_neutral_ghost (A.elim_pure p)

let intro_exists (#a:Type u#a) (p:a -> slprop) (x:erased a)
: stt_ghost unit emp_inames   (p x) (fun _ -> exists* x. p x)
= lift_neutral_ghost (A.intro_exists p x)

let elim_exists (#a:Type u#a) (p:a -> slprop)
: stt_ghost (erased a) emp_inames (exists* x. p x) (fun x -> p x)
= lift_neutral_ghost (A.elim_exists p)

let ghost_reveal (a:Type) (x:erased a)
: stt_ghost a emp_inames emp (fun y -> pure (reveal x == y))
= let m
    : stt_ghost a emp_inames
        (pure (reveal x == reveal x))
        (fun y -> pure (reveal x == y))
    = lift_neutral_ghost (A.return (reveal x))
  in
  pure_trivial (reveal x == reveal x) ();
  m


let dup_inv (i:iref) (p:slprop) = lift_neutral_ghost (A.dup_inv i p)

let new_invariant (p:slprop)
: stt_ghost iref emp_inames p (fun i -> inv i p)
= lift_neutral_ghost (A.new_invariant p)

let fresh_invariant ctx p = lift_neutral_ghost (A.fresh_invariant ctx p)

let inames_live_inv (i:iref) (p:slprop) = lift_neutral_ghost (A.inames_live_inv i p)

let with_invariant #a #fp #fp' #f_opens #p i $f =
  A.with_invariant i f

let with_invariant_g #a #fp #fp' #f_opens #p i $f =
  let f: act (erased a) Ghost f_opens (later p ** fp) (fun x -> later p ** fp' x) = f () in
  A.with_invariant #(erased a) #Ghost #fp #(as_ghost_post fp') #f_opens #p i (fun _ -> f)

let slprop_post_equiv_intro #t (#p #q: t->slprop) (h: (x:t -> squash (p x == q x))) : slprop_post_equiv p q =
  IndefiniteDescription.elim_squash
    (introduce forall x. slprop_equiv (p x) (q x) with
      (h x; Squash.return_squash (slprop_equiv_refl (p x))))

let invariant_name_identifies_invariant p q i j =
  sub_ghost _ _ (slprop_equiv_refl _) (slprop_post_equiv_intro (fun x -> ()))
    (lift_neutral_ghost (A.invariant_name_identifies_invariant p q i))
let later_intro p = lift_neutral_ghost (A.later_intro p)
let later_elim p = lift_neutral_ghost (A.later_elim p)
let implies_elim p q = lift_neutral_ghost (A.implies_elim p q)
let buy1 = A.buy1

let pts_to_not_null #a #p r v = lift_neutral_ghost (A.pts_to_not_null #a #p r v)
let alloc #a #pcm x = A.alloc x
let read r x f = A.read r x f
let write r x y f = A.write r x y f
let share #a #pcm r v0 v1 = lift_neutral_ghost (A.share r v0 v1)
let gather #a #pcm r v0 v1 = lift_neutral_ghost (A.gather r v0 v1)

let ghost_pts_to_not_null #a #p r v = lift_neutral_ghost (A.ghost_pts_to_not_null #a #p r v)
let ghost_alloc #a #pcm x = lift_neutral_ghost <| A.ghost_alloc #a #pcm x
let ghost_read
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
= lift_neutral_ghost <| A.ghost_read r x f

let ghost_write r x y f = lift_neutral_ghost (A.ghost_write r x y f)
let ghost_share r v0 v1 = lift_neutral_ghost (A.ghost_share r v0 v1)
let ghost_gather r v0 v1 = lift_neutral_ghost (A.ghost_gather r v0 v1) 

let big_pts_to_not_null #a #p r v = lift_neutral_ghost (A.big_pts_to_not_null #a #p r v)
let big_alloc #a #pcm x = A.big_alloc x
let big_read r x f = A.big_read r x f
let big_write r x y f = A.big_write r x y f
let big_share #a #pcm r v0 v1 = lift_neutral_ghost (A.big_share r v0 v1)
let big_gather #a #pcm r v0 v1 = lift_neutral_ghost (A.big_gather r v0 v1)


let big_ghost_alloc #a #pcm x = lift_neutral_ghost <| A.big_ghost_alloc #a #pcm x
let big_ghost_read #a #p r x f = lift_neutral_ghost <| A.big_ghost_read r x f
let big_ghost_write r x y f = lift_neutral_ghost (A.big_ghost_write r x y f)
let big_ghost_share r v0 v1 = lift_neutral_ghost (A.big_ghost_share r v0 v1)
let big_ghost_gather r v0 v1 = lift_neutral_ghost (A.big_ghost_gather r v0 v1) 

let nb_pts_to_not_null #a #p r v = lift_neutral_ghost (A.nb_pts_to_not_null #a #p r v)
let nb_alloc #a #pcm x = A.nb_alloc x
let nb_read r x f = A.nb_read r x f
let nb_write r x y f = A.nb_write r x y f
let nb_share #a #pcm r v0 v1 = lift_neutral_ghost (A.nb_share r v0 v1)
let nb_gather #a #pcm r v0 v1 = lift_neutral_ghost (A.nb_gather r v0 v1)


let nb_ghost_alloc #a #pcm x = lift_neutral_ghost <| A.nb_ghost_alloc #a #pcm x
let nb_ghost_read #a #p r x f = lift_neutral_ghost <| A.nb_ghost_read r x f
let nb_ghost_write r x y f = lift_neutral_ghost (A.nb_ghost_write r x y f)
let nb_ghost_share r v0 v1 = lift_neutral_ghost (A.nb_ghost_share r v0 v1)
let nb_ghost_gather r v0 v1 = lift_neutral_ghost (A.nb_ghost_gather r v0 v1) 

let drop p = lift_neutral_ghost (A.drop p)

let equiv_refl a = lift_neutral_ghost (A.equiv_refl a)
let equiv_dup a b = lift_neutral_ghost (A.equiv_dup a b)
let equiv_trans (a b c:slprop) = lift_neutral_ghost (A.equiv_trans a b c)
let equiv_elim (a b:slprop) = lift_neutral_ghost (A.equiv_elim a b)

let slprop_ref_alloc y = lift_neutral_ghost (A.slprop_ref_alloc y)
let slprop_ref_share x y = lift_neutral_ghost (A.slprop_ref_share x y)
let slprop_ref_gather x y1 y2 = lift_neutral_ghost (A.slprop_ref_gather x y1 y2)