module Pulse.Typing.Metatheory

open Pulse.Syntax
open Pulse.Typing

module T = FStar.Tactics.V2

let tot_typing_weakening_single #g #t #ty d x x_t =
  let g1 = singleton_env (fstar_env g) x x_t in
  let g' = mk_env (fstar_env g) in
  assert (equal (push_env g g') g);
  assert (equal (push_env (push_env g g1) g') (push_env g g1));
  assert (equal (push_env g g1) (push_binding g x ppname_default x_t));
  tot_typing_weakening g g' t ty d g1

let st_typing_weakening
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp) (d:st_typing (push_env g g') t c)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : st_typing (push_env g1 g') t c =

  let g2 = diff g1 g in
  let d = st_typing_weakening g g' t c d g2 in
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
    = Pulse.Typing.Metatheory.Base.st_typing_weakening (push_env g g') emp_env t c (coerce_eq () d) g2 in
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
  let d = Pulse.Typing.Metatheory.Base.veq_weakening g g' d g2 in
  assert (equal (push_env (push_env g g2) g') (push_env g1 g'));
  d
