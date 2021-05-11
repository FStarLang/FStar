module Steel.SelEffect.Common

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
open Steel.Semantics.Instantiate
module FExt = FStar.FunctionalExtensionality

let h_exists #a f = VUnit ({hp = Mem.h_exists (fun x -> hp_of (f x)); t = unit; sel = fun _ -> ()})

let can_be_split (p q:vprop) : prop = Mem.slimp (hp_of p) (hp_of q)

let reveal_can_be_split () = ()

let can_be_split_trans p q r = ()
let can_be_split_star_l p q = ()
let can_be_split_star_r p q = ()
let can_be_split_refl p = ()

let equiv (p q:vprop) : prop = Mem.equiv (hp_of p) (hp_of q) /\ True
let reveal_equiv p q = ()

let equiv_can_be_split p1 p2 = ()
let intro_can_be_split_frame p q frame = ()
let can_be_split_post_elim t1 t2 = ()
let equiv_forall_elim t1 t2 = ()

let emp':vprop' =
  { hp = emp;
    t = unit;
    sel = fun _ -> ()}

let reveal_emp () = ()

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

let vdep_hp_payload
  (v: vprop)
  (p: (t_of v -> Tot vprop))
  (h: hmem (hp_of v))
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
  fun (m: hmem (vdep_hp v p)) ->
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
  (fun (h: hmem (normal (hp_of v))) -> f ((normal (sel_of v) <: selector' _ _) h))

let vrewrite_sel_eq
  v #t f h
= ()

let emp_unit_variant p = Mem.emp_unit (hp_of p)
