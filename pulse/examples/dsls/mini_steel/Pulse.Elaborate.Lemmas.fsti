module Pulse.Elaborate.Lemmas
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate

val elab_pure_equiv (#f:RT.fstar_top_env)
                    (#g:env)
                    (#t:pure_term)
                    (#c:pure_comp { C_Tot? c })
                    (d:src_typing f g t c)
  : Lemma (ensures elab_src_typing d == elab_pure t)

val elab_open_commute (t:pure_term) (x:var)
  : Lemma (elab_pure (open_term t x) == RT.open_term (elab_pure t) x)

val elab_comp_close_commute (c:pure_comp) (x:var)
  : Lemma (elab_pure_comp (close_pure_comp c x) == RT.close_term (elab_pure_comp c) x)

val elab_comp_open_commute (c:pure_comp) (x:pure_term)
  : Lemma (elab_pure_comp (open_comp_with c x) == RT.open_with (elab_pure_comp c) (elab_pure x))

