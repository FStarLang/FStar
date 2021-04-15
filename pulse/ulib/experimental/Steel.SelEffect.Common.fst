module Steel.SelEffect.Common

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
module C = Steel.Effect.Common
open Steel.Semantics.Instantiate
module FExt = FStar.FunctionalExtensionality
module Eff = Steel.Effect


let can_be_split (p q:vprop) : prop = Mem.slimp (hp_of p) (hp_of q)

let reveal_can_be_split () = ()

let can_be_split_trans p q r = ()
let can_be_split_star_l p q = ()
let can_be_split_star_r p q = ()
let can_be_split_refl p = ()

let equiv (p q:vprop) : prop = Mem.equiv (hp_of p) (hp_of q) /\ True

let equiv_can_be_split p1 p2 = ()
let intro_can_be_split_frame p q frame = ()
let can_be_split_post_elim t1 t2 = ()
let equiv_forall_elim t1 t2 = ()

let vemp':vprop' =
  { hp = emp;
    t = unit;
    sel = fun _ -> ()}

let reveal_vemp () = ()

let equiv_refl x = ()
let equiv_sym x y = ()
let equiv_trans x y z = ()

let cm_identity x =
  Mem.emp_unit (hp_of x);
  Mem.star_commutative (hp_of x) emp
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
  fun (h: hmem (vrefine_hp v p)) ->
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


let emp_unit_variant p = Mem.emp_unit (hp_of p)
