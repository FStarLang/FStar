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
module I = PulseCore.InstantiatedSemantics
module A = PulseCore.Atomic
module T = FStar.Tactics.V2
module F = FStar.FunctionalExtensionality
open PulseCore.InstantiatedSemantics
open PulseCore.FractionalPermission
open PulseCore.Observability

let double_one_half () = ()
let equate_by_smt = ()
let vprop = slprop
let emp = emp
let op_Star_Star = op_Star_Star
let pure = pure
let op_exists_Star = op_exists_Star
let vprop_equiv = slprop_equiv
let elim_vprop_equiv #p #q pf = slprop_equiv_elim p q
let vprop_post_equiv = slprop_post_equiv
let prop_squash_idem (p:prop)
  : Tot (squash (squash p == p))
  = FStar.PropositionalExtensionality.apply p (squash p)

let intro_vprop_post_equiv
       (#t:Type u#a) 
       (p q: t -> vprop)
       (pf: (x:t -> vprop_equiv (p x) (q x)))
  : vprop_post_equiv p q
  = let pf : squash (forall x. vprop_equiv (p x) (q x)) = 
        introduce forall x. vprop_equiv (p x) (q x)
        with FStar.Squash.return_squash (pf x)
    in
    coerce_eq (prop_squash_idem _) pf

let elim_vprop_post_equiv (#t:Type u#a)
                          (p q: t -> vprop) 
                          (pf:vprop_post_equiv p q)
                          (x:t) 
: vprop_equiv (p x) (q x)
= let pf
    : squash (vprop_equiv (p x) (q x))
    = eliminate forall x. vprop_equiv (p x) (q x) with x
  in
  coerce_eq (prop_squash_idem _) pf

let vprop_equiv_refl (v0:vprop) 
  : vprop_equiv v0 v0
  = slprop_equiv_refl v0

let vprop_equiv_sym (v0 v1:vprop) (p:vprop_equiv v0 v1)
  : vprop_equiv v1 v0
  = slprop_equiv_elim v0 v1; p

let vprop_equiv_trans
      (v0 v1 v2:vprop)
      (p:vprop_equiv v0 v1)
      (q:vprop_equiv v1 v2)
  : vprop_equiv v0 v2
  = slprop_equiv_elim v0 v1;
    slprop_equiv_elim v1 v2;
    p

let vprop_equiv_unit (x:vprop)
  : vprop_equiv (emp ** x) x
  = slprop_equiv_unit x

let vprop_equiv_comm (p1 p2:vprop)
  : vprop_equiv (p1 ** p2) (p2 ** p1)
  = slprop_equiv_comm p1 p2

let vprop_equiv_assoc (p1 p2 p3:vprop)
  : vprop_equiv ((p1 ** p2) ** p3) (p1 ** (p2 ** p3))
  = slprop_equiv_assoc p1 p2 p3

let vprop_equiv_cong (p1 p2 p3 p4:vprop)
                     (f: vprop_equiv p1 p3)
                     (g: vprop_equiv p2 p4)
  : vprop_equiv (p1 ** p2) (p3 ** p4)
  = slprop_equiv_elim p1 p3;
    slprop_equiv_elim p2 p4;
    vprop_equiv_refl _

let vprop_equiv_ext p1 p2 _ = vprop_equiv_refl p1

(* Invariants, just reexport *)
module Act = PulseCore.Action
let iname = Act.iname

let join_sub _ _ = ()
let join_emp is =
  Set.lemma_equal_intro (join_inames is emp_inames) (reveal is);
  Set.lemma_equal_intro (join_inames emp_inames is) (reveal is)

let inv = Act.inv
let name_of_inv = Act.name_of_inv

let add_already_there i is = Set.lemma_equal_intro (add_inv is i) is

////////////////////////////////////////////////////////////////////
// stt a pre post: The main type of a pulse computation
////////////////////////////////////////////////////////////////////
let stt = I.stt
let return_stt_noeq = I.return
let bind_stt = I.bind
let frame_stt = I.frame
let par_stt = I.par
let sub_stt = I.sub
let conv_stt pf1 pf2 = I.conv #_ _ _ _ _ pf1 pf2
let hide_div = I.hide_div

////////////////////////////////////////////////////////////////////
// Atomic computations
////////////////////////////////////////////////////////////////////
let stt_atomic a #obs inames pre post = A.stt_atomic a #obs inames pre post
let lift_observability = A.lift_observability
let return_neutral = A.return_atomic
let return_neutral_noeq = A.return_atomic_noeq
let bind_atomic = A.bind_atomic
let frame_atomic = A.frame_atomic
let sub_atomic = A.sub_atomic
let sub_invs_atomic = A.sub_invs_stt_atomic
let lift_atomic0 = A.lift_atomic0
let lift_atomic1 = A.lift_atomic1
let lift_atomic2 = A.lift_atomic2
let new_invariant = A.new_invariant
let with_invariant = A.with_invariant
let distinct_invariants_have_distinct_names #p #q i j = A.distinct_invariants_have_distinct_names #p #q i j ()
let invariant_name_identifies_invariant #p #q i j = A.invariant_name_identifies_invariant p q i j
////////////////////////////////////////////////////////////////////
// Ghost computations
////////////////////////////////////////////////////////////////////
let stt_ghost = A.stt_ghost
let bind_ghost = A.bind_ghost
let lift_ghost_neutral = A.lift_ghost_neutral
let lift_neutral_ghost = A.lift_neutral_ghost
let frame_ghost = A.frame_ghost
let sub_ghost = A.sub_ghost

//////////////////////////////////////////////////////////////////////////
// Some basic actions and ghost operations
//////////////////////////////////////////////////////////////////////////

let rewrite p q (pf:vprop_equiv p q)
  : stt_ghost unit p (fun _ -> q)
  = slprop_equiv_elim p q;
    A.noop q

#push-options "--no_tactics"
let rewrite_by (p:vprop) (q:vprop) 
               (t:unit -> T.Tac unit)
               (_:unit { T.with_tactic t (vprop_equiv p q) })
  : stt_ghost unit p (fun _ -> q)
  = let pf : squash (vprop_equiv p q) = T.by_tactic_seman t (vprop_equiv p q) in
    prop_squash_idem (vprop_equiv p q);
    rewrite p q (coerce_eq () pf)
#pop-options

let elim_pure_explicit p = A.elim_pure p
let elim_pure _ #p = A.elim_pure p
let intro_pure p _ = A.intro_pure p ()
let elim_exists #a p = A.elim_exists p
let intro_exists #a p e = A.intro_exists p e
let intro_exists_erased #a p e = A.intro_exists p e

let stt_ghost_reveal a x = A.ghost_reveal a x
let stt_admit _ _ _ = admit () //intentional
let stt_atomic_admit _ _ _ = admit () //intentional
let stt_ghost_admit _ _ _ = admit () //intentional

    
let assert_ (p:vprop) = A.noop p
let assume_ (p:vprop) = admit() //intentional
let drop_ (p:vprop) = A.drop p

let unreachable (#a:Type) (#p:vprop) (#q:a -> vprop) (_:squash False)
  : stt_ghost a p q
  = let v = FStar.Pervasives.false_elim #a () in
    let m = A.return_ghost v q in
    coerce_eq () m

let elim_false (a:Type) (p:a -> vprop) =
  A.bind_ghost
    (A.noop (pure False))
    (fun _ -> A.bind_ghost (A.elim_pure False) unreachable )

//////////////////////////////////////////////////////////////////////////
// References
//////////////////////////////////////////////////////////////////////////
let pcm_ref #a p = PulseCore.Action.ref a p

let pcm_pts_to (#a:Type u#1) (#p:pcm a) (r:pcm_ref p) (v:a) =
  PulseCore.Action.pts_to r v

let pcm_ref_null #a p = PulseCore.Action.ref_null #a p
let is_pcm_ref_null #a #p r = PulseCore.Action.is_ref_null #a #p r
let pts_to_not_null #a #p r v = A.pts_to_not_null #a #p r v

let alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:a{compatible pcm x x /\ pcm.refine x})
: stt (pcm_ref pcm)
    emp
    (fun r -> pcm_pts_to r x)
= A.lift_atomic0 (A.alloc #a #pcm x)

let read
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
= A.lift_atomic1 (A.read r x f)

let write
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt unit
    (pcm_pts_to r x)
    (fun _ -> pcm_pts_to r y)
= A.lift_atomic0 (A.write r x y f)

let share = A.share
let gather = A.gather

////////////////////////////////////////////////////////
// ghost refs
////////////////////////////////////////////////////////
let ghost_pcm_ref #a p = A.ghost_ref #a p
let ghost_pcm_pts_to #a #p r v = A.ghost_pts_to #a #p r v
let ghost_alloc = A.ghost_alloc
let ghost_read = A.ghost_read
let ghost_write = A.ghost_write
let ghost_share = A.ghost_share
let ghost_gather = A.ghost_gather

let return_stt_alt (#a:Type u#a) (x:a) (p:a -> vprop)
: stt a (p x ** pure (x == x)) (fun v -> p v ** pure (v == x))
= return x (fun v -> p v ** pure (v == x))

let refl_stt (#a:Type u#a) (x:a)
: stt unit emp (fun _ -> pure (x == x))
= let m : stt_ghost unit emp (fun _ -> pure (x == x)) = intro_pure (x == x) () in
  let m : stt_atomic unit #Neutral emp_inames emp (fun _ -> pure (x == x)) = lift_ghost_neutral m unit_non_informative in
  lift_atomic0 m

let frame_flip (#pre #a #post:_) (frame:slprop) (e:stt a pre post)
: stt a (pre ** frame) (fun x -> frame ** post x)
= let i
  : vprop_post_equiv (fun x -> post x ** frame) (fun x -> frame ** post x)
  = intro_vprop_post_equiv _ _ (fun x -> vprop_equiv_comm (post x) frame)
  in
  sub_stt _ _ (vprop_equiv_refl _) i (frame_stt frame e)

let return_stt_a (#a:Type u#a) (x:a) (p:a -> vprop)
: stt unit (p x) (fun _ -> p x ** pure (x == x))
= elim_vprop_equiv (vprop_equiv_comm (p x) emp);
  elim_vprop_equiv (vprop_equiv_unit (p x));
  frame_flip (p x) (refl_stt x)

let return_stt (#a:Type u#a) (x:a) (p:a -> vprop)
: stt a (p x) (fun v -> p v ** pure (v == x))
= bind_stt (return_stt_a x p) (fun _ -> return_stt_alt x p)

let as_atomic #a pre post (e:stt a pre post) = admit() //intentional