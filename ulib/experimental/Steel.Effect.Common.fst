(*
   Copyright 2020 Microsoft Research

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

module Steel.Effect.Common
module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
open Steel.Semantics.Instantiate
module FExt = FStar.FunctionalExtensionality

let h_exists #a f = VUnit ({hp = Mem.h_exists (fun x -> hp_of (f x)); t = unit; sel = fun _ -> ()})

let can_be_split (p q:vprop) : prop = Mem.slimp (hp_of p) (hp_of q)

let reveal_can_be_split () = ()

let can_be_split_interp r r' h = ()

let can_be_split_trans p q r = ()
let can_be_split_star_l p q = ()
let can_be_split_star_r p q = ()
let can_be_split_refl p = ()

let can_be_split_congr_l p q r =
  Classical.forall_intro (interp_star (hp_of p) (hp_of r));
  Classical.forall_intro (interp_star (hp_of q) (hp_of r))

let can_be_split_congr_r p q r =
  Classical.forall_intro (interp_star (hp_of r) (hp_of p));
  Classical.forall_intro (interp_star (hp_of r) (hp_of q))

let equiv (p q:vprop) : prop = Mem.equiv (hp_of p) (hp_of q) /\ True
let reveal_equiv p q = ()

let valid_rmem (#frame:vprop) (h:rmem' frame) : prop =
  forall (p p1 p2:vprop). can_be_split frame p /\ p == VStar p1 p2 ==>
     (h p1, h p2) == h (VStar p1 p2)

let lemma_valid_mk_rmem (r:vprop) (h:hmem r) = ()

let reveal_mk_rmem (r:vprop) (h:hmem r) (r0:vprop{r `can_be_split` r0})
  : Lemma ((mk_rmem r h) r0 == sel_of r0 h)
  = FExt.feq_on_domain_g (unrestricted_mk_rmem r h)

let emp':vprop' =
  { hp = emp;
    t = unit;
    sel = fun _ -> ()}
let emp = VUnit emp'

let reveal_emp () = ()

let lemma_valid_focus_rmem #r h r0 =
  Classical.forall_intro (Classical.move_requires (can_be_split_trans r r0))

let rec lemma_frame_refl' (frame:vprop) (h0:rmem frame) (h1:rmem frame)
  : Lemma ((h0 frame == h1 frame) <==> frame_equalities' frame h0 h1)
  = match frame with
    | VUnit _ -> ()
    | VStar p1 p2 ->
      can_be_split_star_l p1 p2;
      can_be_split_star_r p1 p2;

      let h01 : rmem p1 = focus_rmem h0 p1 in
      let h11 : rmem p1 = focus_rmem h1 p1 in
      let h02 = focus_rmem h0 p2 in
      let h12 = focus_rmem h1 p2 in


      lemma_frame_refl' p1 h01 h11;
      lemma_frame_refl' p2 h02 h12

let lemma_frame_equalities frame h0 h1 p =
  let p1 : prop = h0 frame == h1 frame in
  let p2 : prop = frame_equalities' frame h0 h1 in
  lemma_frame_refl' frame h0 h1;
  FStar.PropositionalExtensionality.apply p1 p2

let lemma_frame_emp h0 h1 p =
  FStar.PropositionalExtensionality.apply True (h0 (VUnit emp') == h1 (VUnit emp'))

let elim_conjunction p1 p1' p2 p2' = ()

let can_be_split_dep_refl p = ()
let equiv_can_be_split p1 p2 = ()
let intro_can_be_split_frame p q frame = ()
let can_be_split_post_elim t1 t2 = ()
let equiv_forall_refl t = ()
let equiv_forall_elim t1 t2 = ()

let equiv_refl x = ()
let equiv_sym x y = ()
let equiv_trans x y z = ()

let cm_identity x =
  Mem.emp_unit (hp_of x);
  Mem.star_commutative (hp_of x) Mem.emp
let star_commutative p1 p2 = Mem.star_commutative (hp_of p1) (hp_of p2)
let star_associative p1 p2 p3 = Mem.star_associative (hp_of p1) (hp_of p2) (hp_of p3)
let star_congruence p1 p2 p3 p4 = Mem.star_congruence (hp_of p1) (hp_of p2) (hp_of p3) (hp_of p4)

let vrefine_am (v: vprop) (p: (t_of v -> Tot prop)) : Tot (a_mem_prop (hp_of v)) =
  fun h -> p (sel_of v h)

let vrefine_hp
  v p
= refine_slprop (hp_of v) (vrefine_am v p)

let interp_vrefine_hp
  v p m
= ()

let vrefine_sel' (v: vprop) (p: (t_of v -> Tot prop)) : Tot (selector' (vrefine_t v p) (vrefine_hp v p))
=
  fun (h: Mem.hmem (vrefine_hp v p)) ->
    interp_refine_slprop (hp_of v) (vrefine_am v p) h;
    sel_of v h

let vrefine_sel
  v p
= assert (sel_depends_only_on (vrefine_sel' v p));
  assert (sel_depends_only_on_core (vrefine_sel' v p));
  vrefine_sel' v p

let vrefine_sel_eq
  v p m
= ()

let vdep_hp_payload
  (v: vprop)
  (p: (t_of v -> Tot vprop))
  (h: Mem.hmem (hp_of v))
: Tot slprop
= hp_of (p (sel_of v h))

let vdep_hp
  v p
=
  sdep (hp_of v) (vdep_hp_payload v p)

let interp_vdep_hp
  v p m
=
  interp_sdep (hp_of v) (vdep_hp_payload v p) m;
  let left = interp (vdep_hp v p) m in
  let right = interp (hp_of v) m /\ interp (hp_of v `Mem.star` hp_of (p (sel_of v m))) m in
  let f ()
  : Lemma
    (requires left)
    (ensures right)
  = interp_star (hp_of v) (hp_of (p (sel_of v m))) m
  in
  let g ()
  : Lemma
    (requires right)
    (ensures left)
  = interp_star (hp_of v) (hp_of (p (sel_of v m))) m
  in
  Classical.move_requires f ();
  Classical.move_requires g ()

let vdep_sel'
  (v: vprop)
  (p: t_of v -> Tot vprop)
: Tot (selector' (vdep_t v p) (vdep_hp v p))
=
  fun (m: Mem.hmem (vdep_hp v p)) ->
    interp_vdep_hp v p m;
    let x = sel_of v m in
    let y = sel_of (p (sel_of v m)) m in
    (| x, y |)

let vdep_sel
  v p
= Classical.forall_intro_2 (Classical.move_requires_2 (fun (m0 m1: mem) -> (join_commutative m0) m1));
  vdep_sel' v p

let vdep_sel_eq
  v p m
= Classical.forall_intro_2 (Classical.move_requires_2 (fun (m0 m1: mem) -> (join_commutative m0) m1));
  ()

let vrewrite_sel
  v #t f
=
  (fun (h: Mem.hmem (normal (hp_of v))) -> f ((normal (sel_of v) <: selector' _ _) h))

let vrewrite_sel_eq
  v #t f h
= ()

let solve_can_be_split_for _ = ()
let solve_can_be_split_lookup = ()

let emp_unit_variant p = Mem.emp_unit (hp_of p)

let solve_can_be_split_forall_dep_for _ = ()
let solve_can_be_split_forall_dep_lookup = ()
