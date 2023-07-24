module Pulse.Checker.Prover.Util

open Pulse.Syntax
open Pulse.Typing

module T = FStar.Tactics.V2
module Metatheory = Pulse.Typing.Metatheory
module PS = Pulse.Checker.Prover.Substs

let st_typing_subst (g:env) (uvs:env { disjoint uvs g }) (t:st_term) (c:comp_st)
  (d:st_typing (push_env g uvs) t c)
  (ss:PS.ss_t)

  : T.Tac (option (st_typing g (PS.ss_st_term t ss) (PS.ss_comp c ss))) =

  let nts_opt = PS.ss_to_nt_substs g uvs ss in
  match nts_opt with
  | None -> None
  | Some nts ->
    let g' = mk_env (fstar_env g) in
    assert (equal (push_env uvs g') uvs);
    let d = PS.st_typing_nt_substs g uvs g' d nts in
    assume (equal (push_env g (PS.nt_subst_env g' nts)) g);
    Some d

let st_typing_weakening
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp) (d:st_typing (push_env g g') t c)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : st_typing (push_env g1 g') t c =

  let g2 = diff g1 g in
  let d = Metatheory.st_typing_weakening g g' t c d g2 in
  assert (equal (push_env (push_env g g2) g') (push_env g1 g'));
  d

let st_typing_weakening_standard
  (#g:env) (#t:st_term) (#c:comp) (d:st_typing g t c)
  (g1:env { g1 `env_extends` g })
  : st_typing g1 t c =

  let g' = mk_env (fstar_env g) in
  assert (equal (push_env g g') g);
  let d = st_typing_weakening g g' t c d g1 in
  assert (equal (push_env g1 g') g1);
  d

let st_typing_weakening_end
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp) (d:st_typing (push_env g g') t c)
  (g'':env { g'' `env_extends` g' /\ disjoint g'' g })
  : st_typing (push_env g g'') t c =

  let g2 = diff g'' g' in
  let emp_env = mk_env (fstar_env g) in
  assert (equal (push_env g g')
                (push_env (push_env g g') emp_env));
  let d
    : st_typing (push_env (push_env (push_env g g') g2) emp_env) _ _
    = Pulse.Typing.Metatheory.st_typing_weakening (push_env g g') emp_env t c (coerce_eq () d) g2 in
  assert (equal (push_env (push_env (push_env g g') g2) emp_env)
                (push_env (push_env g g') g2));
  push_env_assoc g g' g2;
  assert (equal (push_env (push_env g g') g2)
                (push_env g (push_env g' g2)));
  assert (equal (push_env g (push_env g' g2))
                (push_env g g''));
  coerce_eq () d

let veq_weakening
  (g:env) (g':env { disjoint g g' })
  (#v1 #v2:vprop) (d:vprop_equiv (push_env g g') v1 v2)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : vprop_equiv (push_env g1 g') v1 v2 =

  let g2 = diff g1 g in
  let d = Metatheory.veq_weakening g g' d g2 in
  assert (equal (push_env (push_env g g2) g') (push_env g1 g'));
  d

let debug_prover _ _ = ()