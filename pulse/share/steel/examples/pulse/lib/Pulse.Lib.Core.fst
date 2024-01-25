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

let double_one_half () = ()
let equate_by_smt = ()
let vprop = slprop
let emp = emp
let op_Star_Star = op_Star_Star
let pure = pure
let op_exists_Star = op_exists_Star
let vprop_equiv = slprop_equiv
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

let stt (a:Type u#a) (pre:vprop) (post:a -> vprop)
   = stt a pre post

let inames_disj = Act.inames_disj

type stt_unobservable (a:Type u#a) (opens:inames) (pre:vprop) (post:a -> vprop) =
  A.stt_atomic a #A.Unobservable opens pre post

type stt_atomic (a:Type u#a) (opens:inames) (pre:vprop) (post:a -> vprop) =
  A.stt_atomic a #A.Observable opens pre post
 
type stt_ghost (a:Type u#a) (opens:inames) (pre:vprop) (post:a -> vprop) =
  A.stt_ghost a opens pre post
 
let return_stt (#a:Type u#a) (x:a) (p:a -> vprop) = admit() //I.return x p
let return (#a:Type u#a) (x:a) (p:a -> vprop) = I.return x p
let return_stt_ghost (#a:Type u#a) (x:a) (p:a -> vprop) = A.return_ghost x p
let return_stt_ghost_noeq (#a:Type u#a) (x:a) (p:a -> vprop) = admit() 
let bind_stt = I.bind

let lift_stt_atomic0 #a #opens #pre #post e =
  A.(lift_atomic0 #_ #Observable #opens #pre #post e)
let lift_stt_atomic1 #a #opens #pre #post e =
  A.(lift_atomic1 #_ #Observable #opens #pre #post e)
let lift_stt_atomic2 #a #opens #pre #post e =
  A.(lift_atomic2 #_ #Observable #opens #pre #post e)

let bind_sttg = A.bind_ghost

let bind_stt_atomic_ghost #a #b #opens #pre1 #post1 #post2 e1 e2 reveal_b =
  A.bind_atomic e1 (fun x -> A.lift_ghost (e2 x) reveal_b)

let bind_stt_ghost_atomic #a #b #opened #pre1 #post1 #post2 e1 e2 reveal_a =
  A.bind_atomic (A.lift_ghost e1 reveal_a) e2

#push-options "--print_implicits"
let lift_stt_ghost #a #opened #pre #post e reveal_a =
  admit() //A.lift_ghost e reveal_a; coerce Unobservable to Observable

let frame_stt = I.frame
    
let frame_stt_atomic frame e = A.frame_atomic frame e
    
let frame_stt_ghost = A.frame_ghost

let sub_stt = I.sub

let sub_stt_atomic pre2 post2 pf1 pf2 e =
   A.sub_atomic pre2 post2 pf1 pf2 e

let sub_invs_stt_atomic e pf = A.sub_invs_stt_atomic e pf
let sub_invs_stt_unobservable e pf = A.sub_invs_stt_atomic e pf

let sub_stt_ghost = A.sub_ghost

let sub_invs_stt_ghost = A.sub_invs_stt_ghost

let return_stt_unobservable #a x p = A.return_atomic x p

let return_stt_unobservable_noeq #a x (p:(a -> vprop)) = admit()

let new_invariant p = A.new_invariant p

let new_invariant' p = admit()

let with_invariant_g (#a:Type)
                     (#fp:vprop)
                     (#fp':a -> vprop)
                     (#f_opens:inames)
                     (#p:vprop)
                     (pf:non_informative_witness a)
                     (i:inv p{not (mem_inv f_opens i)})
                     ($f: unit -> stt_ghost a f_opens (p ** fp) (fun x -> p ** fp' x))
: stt_unobservable a (add_inv f_opens i) fp fp'
= let f = fun _ -> A.lift_ghost (f ()) pf in
  A.with_invariant i f

let with_invariant_a i f = A.with_invariant i f

let rewrite p q (pf:vprop_equiv p q)
  : stt_ghost unit emp_inames p (fun _ -> q)
  = slprop_equiv_elim p q;
    A.noop q

#push-options "--no_tactics"
let rewrite_by (p:vprop) (q:vprop) 
               (t:unit -> T.Tac unit)
               (_:unit { T.with_tactic t (vprop_equiv p q) })
  : stt_ghost unit emp_inames p (fun _ -> q)
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

let elim_forall #a = admit()
let intro_forall #a = admit()

let while_loop inv cond body = admit()

let stt_ghost_reveal a x = A.ghost_reveal a x
let stt_admit _ _ _ = admit ()
let stt_atomic_admit _ _ _ = admit ()
let stt_ghost_admit _ _ _ = admit ()

let stt_par = I.par
    
let assert_ (p:vprop) = A.noop p
let assume_ (p:vprop) = admit()
let drop_ (p:vprop) = admit()

let unreachable (#a:Type) (#p:vprop) (#q:a -> vprop) (_:squash False)
  : stt_ghost a emp_inames p q
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
