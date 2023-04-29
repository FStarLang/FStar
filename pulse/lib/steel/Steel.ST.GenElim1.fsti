module Steel.ST.GenElim1
include Steel.ST.GenElim1.Base

module T = FStar.Tactics

val gen_elim'
  (#opened: _)
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
  (sq: squash (gen_elim_prop_placeholder enable_nondep_opt p a q post))
  (_: unit)
: STGhost (Ghost.erased a) opened p (fun x -> guard_vprop (q x)) (gen_elim_prop enable_nondep_opt p a q post) post

val gen_elim
  (#opened: _)
  (#[@@@ framing_implicit] p: vprop)
  (#[@@@ framing_implicit] a: Type)
  (#[@@@ framing_implicit] q: Ghost.erased a -> Tot vprop)
  (#[@@@ framing_implicit] post: Ghost.erased a -> Tot prop)
  (#[@@@ framing_implicit] sq: squash (gen_elim_prop_placeholder true p a q post))
  (_: unit)
: STGhostF (Ghost.erased a) opened p (fun x -> guard_vprop (q x)) ( (T.with_tactic solve_gen_elim_prop) (squash (gen_elim_prop true p a q post))) post

val gen_elim_dep
  (#opened: _)
  (#[@@@ framing_implicit] p: vprop)
  (#[@@@ framing_implicit] a: Type)
  (#[@@@ framing_implicit] q: Ghost.erased a -> Tot vprop)
  (#[@@@ framing_implicit] post: Ghost.erased a -> Tot prop)
  (#[@@@ framing_implicit] sq: squash (gen_elim_prop_placeholder false p a q post))
  (_: unit)
: STGhostF (Ghost.erased a) opened p (fun x -> guard_vprop (q x)) ( (T.with_tactic solve_gen_elim_prop) (squash (gen_elim_prop false p a q post))) post
