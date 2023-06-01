module Pulse.Elaborate
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
include Pulse.Elaborate.Core
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Elaborate.Pure
open Pulse.Typing

val elab_open_commute' (e:term)
                       (v:term)
                       (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_term e) (RT.OpenWith (elab_term v)) n ==
              elab_term (open_term' e v n))

val elab_close_commute' (e:term)
                        (v:var)
                        (n:index)
  : Lemma (RT.open_or_close_term' (elab_term e) (RT.CloseVar v) n ==
           elab_term (close_term' e v n))

val elab_open_commute (t:term) (x:var)
  : Lemma (elab_term (open_term t x) == RT.open_term (elab_term t) x)

val elab_comp_close_commute (c:comp) (x:var)
  : Lemma (elab_comp (close_comp c x) == RT.close_term (elab_comp c) x)

val elab_comp_open_commute (c:comp) (x:term)
  : Lemma (elab_comp (open_comp_with c x) == RT.open_with (elab_comp c) (elab_term x))

val elab_ln (t:term) (i:int)
  : Lemma (requires ln' t i)
          (ensures RT.ln' (elab_term t) i)

val elab_ln_comp (c:comp) (i:int)
  : Lemma (requires ln_c' c i) (ensures RT.ln' (elab_comp c) i)

val elab_freevars (e:term)
  : Lemma (freevars e == RT.freevars (elab_term e))
