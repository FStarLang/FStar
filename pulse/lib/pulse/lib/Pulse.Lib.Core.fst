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
module CM = FStar.Algebra.CommMonoid
open PulseCore.InstantiatedSemantics
open PulseCore.FractionalPermission
open PulseCore.Observability

let equate_by_smt = ()
let equate_strict = ()
let equate_syntactic = ()

let allow_ambiguous = ()

let slprop = slprop
let slprop2_base = slprop2_base
let cm_slprop2 = cm_slprop2
let down2 = down2
let up2 = up2
let up2_is_slprop2 = up2_is_slprop2
let slprop1_base = slprop1_base
let cm_slprop1 = cm_slprop1
let down1 = down1
let up1 = up1
let up1_is_slprop1 = up1_is_slprop1

let slprop_1_is_2 = slprop_1_is_2

let emp = emp
let emp_is_slprop1 = ()
let pure = pure
let pure_is_slprop1 p = ()
let op_Star_Star = op_Star_Star
let slprop2_star p q = slprop2_star p q
let slprop1_star p q = slprop1_star p q
let op_exists_Star = op_exists_Star
let slprop2_exists #a p = slprop2_exists #a p
let slprop1_exists #a p = slprop1_exists #a p
let up2_emp    = up2_emp
let down2_emp  = down2_emp
let up2_star   = up2_star
let down2_star = down2_star
let up1_emp    = up1_emp
let down1_emp  = down1_emp
let up1_star   = up1_star
let down1_star = down1_star
let slprop_equiv = slprop_equiv
let elim_slprop_equiv #p #q pf = slprop_equiv_elim p q
let slprop_post_equiv = slprop_post_equiv
let prop_squash_idem (p:prop)
  : Tot (squash (squash p == p))
  = FStar.PropositionalExtensionality.apply p (squash p)

let intro_slprop_post_equiv
       (#t:Type u#a) 
       (p q: t -> slprop)
       (pf: (x:t -> slprop_equiv (p x) (q x)))
  : slprop_post_equiv p q
  = let pf : squash (forall x. slprop_equiv (p x) (q x)) = 
        introduce forall x. slprop_equiv (p x) (q x)
        with FStar.Squash.return_squash (pf x)
    in
    coerce_eq (prop_squash_idem _) pf

let elim_slprop_post_equiv (#t:Type u#a)
                          (p q: t -> slprop) 
                          (pf:slprop_post_equiv p q)
                          (x:t) 
: slprop_equiv (p x) (q x)
= let pf
    : squash (slprop_equiv (p x) (q x))
    = eliminate forall x. slprop_equiv (p x) (q x) with x
  in
  coerce_eq (prop_squash_idem _) pf

let slprop_equiv_refl (v0:slprop) 
  : slprop_equiv v0 v0
  = slprop_equiv_refl v0

let slprop_equiv_sym (v0 v1:slprop) (p:slprop_equiv v0 v1)
  : slprop_equiv v1 v0
  = slprop_equiv_elim v0 v1; p

let slprop_equiv_trans
      (v0 v1 v2:slprop)
      (p:slprop_equiv v0 v1)
      (q:slprop_equiv v1 v2)
  : slprop_equiv v0 v2
  = slprop_equiv_elim v0 v1;
    slprop_equiv_elim v1 v2;
    p

let slprop_equiv_unit (x:slprop)
  : slprop_equiv (emp ** x) x
  = slprop_equiv_unit x

let slprop_equiv_comm (p1 p2:slprop)
  : slprop_equiv (p1 ** p2) (p2 ** p1)
  = slprop_equiv_comm p1 p2

let slprop_equiv_assoc (p1 p2 p3:slprop)
  : slprop_equiv ((p1 ** p2) ** p3) (p1 ** (p2 ** p3))
  = slprop_equiv_assoc p1 p2 p3

let slprop_equiv_exists (#a:Type) (p q : a -> slprop)
  (_ : squash (forall x. slprop_equiv (p x) (q x)))
  : slprop_equiv (op_exists_Star p) (op_exists_Star q)
  = slprop_equiv_exists p q ()

let slprop_equiv_cong (p1 p2 p3 p4:slprop)
                     (f: slprop_equiv p1 p3)
                     (g: slprop_equiv p2 p4)
  : slprop_equiv (p1 ** p2) (p3 ** p4)
  = slprop_equiv_elim p1 p3;
    slprop_equiv_elim p2 p4;
    slprop_equiv_refl _

let slprop_equiv_ext p1 p2 _ = slprop_equiv_refl p1

(* Invariants, just reexport *)
module Act = PulseCore.Action
let iname = Act.iname

let join_sub _ _ = ()
let join_emp is =
  Set.lemma_equal_intro (join_inames is emp_inames) (reveal is);
  Set.lemma_equal_intro (join_inames emp_inames is) (reveal is)

let iref = Act.iref
instance non_informative_iref = {
  reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer iref;
}
let inv i p = Act.(inv i p)
let iname_of i = Act.iname_of i
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
let lift_atomic3 = A.lift_atomic3

////////////////////////////////////////////////////////////////////
// Ghost computations
////////////////////////////////////////////////////////////////////
let stt_ghost = A.stt_ghost
let bind_ghost = A.bind_ghost
(* lift_ghost_neutral takes a dictionary argument in Core, but just a revealer
function internally in the model, hence we project it away. *)
let lift_ghost_neutral #a #pre #post e ni_a = A.lift_ghost_neutral #a #pre #post e ni_a.reveal
let lift_neutral_ghost = A.lift_neutral_ghost
let frame_ghost = A.frame_ghost
let sub_ghost = A.sub_ghost
let sub_invs_ghost = A.sub_invs_stt_ghost

////////////////////////////////////////////////////////////////////
// Invariants
////////////////////////////////////////////////////////////////////
let dup_inv = A.dup_inv
let new_invariant = A.new_invariant
let fresh_wrt = PulseCore.Action.fresh_wrt
let fresh_wrt_def i c = ()
let all_live = Act.all_live
let all_live_nil () = ()

let live_eq (i:iref)
  : Lemma (Act.live i == (exists* (p:slprop). inv i p)) =
  calc (==) {
    Act.live i;
  (==) { _ by (T.trefl ()) }
    exists* (p:slprop). inv i p;
  }
let all_live_cons hd tl = live_eq hd
let fresh_invariant = A.fresh_invariant
let with_invariant = A.with_invariant
let with_invariant_g = A.with_invariant_g
let distinct_invariants_have_distinct_names #p #q i j _ = A.distinct_invariants_have_distinct_names #p #q i j _
let invariant_name_identifies_invariant #p #q i j = A.invariant_name_identifies_invariant p q i j

//////////////////////////////////////////////////////////////////////////
// Some basic actions and ghost operations
//////////////////////////////////////////////////////////////////////////

let rewrite p q (pf:slprop_equiv p q)
  : stt_ghost unit emp_inames p (fun _ -> q)
  = slprop_equiv_elim p q;
    A.noop q

#push-options "--no_tactics"
let rewrite_by (p:slprop) (q:slprop) 
               (t:unit -> T.Tac unit)
               (_:unit { T.with_tactic t (slprop_equiv p q) })
  : stt_ghost unit emp_inames p (fun _ -> q)
  = let pf : squash (slprop_equiv p q) = T.by_tactic_seman t (slprop_equiv p q) in
    prop_squash_idem (slprop_equiv p q);
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

    
let assert_ (p:slprop) = A.noop p
let assume_ (p:slprop) = admit() //intentional
let drop_ (p:slprop) = A.drop p

let unreachable (#a:Type) (#p:slprop) (#q:a -> slprop) (_:squash False)
  : stt_ghost a emp_inames p q
  = let v = FStar.Pervasives.false_elim #a () in
    let m = A.return_ghost v q in
    coerce_eq () m

let elim_false (a:Type) (p:a -> slprop) =
  A.bind_ghost
    (A.noop (pure False))
    (fun _ -> A.bind_ghost (A.elim_pure False) unreachable )

//////////////////////////////////////////////////////////////////////////
// References
//////////////////////////////////////////////////////////////////////////
let core_pcm_ref = PulseCore.Action.core_ref
let null_core_pcm_ref = PulseCore.Action.core_ref_null
let is_null_core_pcm_ref r = PulseCore.Action.is_core_ref_null r

let pcm_pts_to (#a:Type u#1) (#p:pcm a) (r:pcm_ref p) (v:a) =
  PulseCore.Action.pts_to #a #p r v
let is_slprop1_pcm_pts_to #a #p r v = ()
let pts_to_not_null #a #p r v = A.pts_to_not_null #a #p r v

let alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
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
let core_ghost_pcm_ref = PulseCore.Action.core_ghost_ref

instance non_informative_ghost_pcm_ref a p = {
  reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer (ghost_pcm_ref p);
}

let ghost_pcm_pts_to #a #p r v = PulseCore.Action.ghost_pts_to #a #p r v
let is_slprop1_ghost_pcm_pts_to #a #p r v = ()
let ghost_alloc = A.ghost_alloc
let ghost_read = A.ghost_read
let ghost_write = A.ghost_write
let ghost_share = A.ghost_share
let ghost_gather = A.ghost_gather

let return_stt_alt (#a:Type u#a) (x:a) (p:a -> slprop)
: stt a (p x ** pure (x == x)) (fun v -> p v ** pure (v == x))
= return x (fun v -> p v ** pure (v == x))

let refl_stt (#a:Type u#a) (x:a)
: stt unit emp (fun _ -> pure (x == x))
= let m : stt_ghost unit emp_inames emp (fun _ -> pure (x == x)) = intro_pure (x == x) () in
  let m : stt_atomic unit #Neutral emp_inames emp (fun _ -> pure (x == x)) = lift_ghost_neutral m FStar.Tactics.Typeclasses.solve in
  lift_atomic0 m

let frame_flip (#pre #a #post:_) (frame:slprop) (e:stt a pre post)
: stt a (pre ** frame) (fun x -> frame ** post x)
= let i
  : slprop_post_equiv (fun x -> post x ** frame) (fun x -> frame ** post x)
  = intro_slprop_post_equiv _ _ (fun x -> slprop_equiv_comm (post x) frame)
  in
  sub_stt _ _ (slprop_equiv_refl _) i (frame_stt frame e)

let return_stt_a (#a:Type u#a) (x:a) (p:a -> slprop)
: stt unit (p x) (fun _ -> p x ** pure (x == x))
= elim_slprop_equiv (slprop_equiv_comm (p x) emp);
  elim_slprop_equiv (slprop_equiv_unit (p x));
  frame_flip (p x) (refl_stt x)

let return_stt (#a:Type u#a) (x:a) (p:a -> slprop)
: stt a (p x) (fun v -> p v ** pure (v == x))
= bind_stt (return_stt_a x p) (fun _ -> return_stt_alt x p)

////////////////////////////////////////////////////////
// big refs
////////////////////////////////////////////////////////
let big_pcm_pts_to #a #p r v = PulseCore.Action.big_pts_to #a #p r v
let is_slprop2_big_pcm_pts_to _ _ = ()
let big_pts_to_not_null #a #p r v = A.big_pts_to_not_null #a #p r v

let big_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: stt (pcm_ref pcm)
    emp
    (fun r -> big_pcm_pts_to r x)
= A.lift_atomic0 (A.big_alloc #a #pcm x)

let big_read
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt (v:a{compatible p x v /\ p.refine v})
    (big_pcm_pts_to r x)
    (fun v -> big_pcm_pts_to r (f v))
= A.lift_atomic2 (A.big_read r x f)

let big_write
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt unit
    (big_pcm_pts_to r x)
    (fun _ -> big_pcm_pts_to r y)
= A.lift_atomic0 (A.big_write r x y f)

let big_share = A.big_share
let big_gather = A.big_gather

let big_ghost_pcm_pts_to #a #p r v = PulseCore.Action.big_ghost_pts_to #a #p r v
let is_slprop2_big_ghost_pcm_pts_to _ _ = ()
let big_ghost_alloc = A.big_ghost_alloc
let big_ghost_read = A.big_ghost_read
let big_ghost_write = A.big_ghost_write
let big_ghost_share = A.big_ghost_share
let big_ghost_gather = A.big_ghost_gather

////////////////////////////////////////////////////////
// non-boxable refs
////////////////////////////////////////////////////////
let nb_pcm_pts_to #a #p r v = PulseCore.Action.nb_pts_to #a #p r v
let nb_pts_to_not_null #a #p r v = A.nb_pts_to_not_null #a #p r v

let nb_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: stt (pcm_ref pcm)
    emp
    (fun r -> nb_pcm_pts_to r x)
= A.lift_atomic0 (A.nb_alloc #a #pcm x)

let nb_read
    (#a:Type u#3)
    (#p:pcm a)
    (r:pcm_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt (v:a{compatible p x v /\ p.refine v})
    (nb_pcm_pts_to r x)
    (fun v -> nb_pcm_pts_to r (f v))
= A.lift_atomic3 (A.nb_read #a #p r x f)

let nb_write
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt unit
    (nb_pcm_pts_to r x)
    (fun _ -> nb_pcm_pts_to r y)
= A.lift_atomic0 (A.nb_write r x y f)

let nb_share = A.nb_share
let nb_gather = A.nb_gather

let nb_ghost_pcm_pts_to #a #p r v = PulseCore.Action.nb_ghost_pts_to #a #p r v
let nb_ghost_alloc = A.nb_ghost_alloc
let nb_ghost_read = A.nb_ghost_read
let nb_ghost_write = A.nb_ghost_write
let nb_ghost_share = A.nb_ghost_share
let nb_ghost_gather = A.nb_ghost_gather

let as_atomic #a pre post (e:stt a pre post) = admit () // intentional since it is an assumption
