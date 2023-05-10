module Pulse.Checker.Pure
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Readback
module RTB = FStar.Tactics.Builtins

val instantiate_term_implicits (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (term & term)

val check_universe (f0:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (u:universe & universe_of f0 g t u)

val check_term (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (t:term &
           ty:term &
           typing f g t ty)

val check_term_and_type (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (t:term  &
           u:universe &
           ty:term &
           universe_of f g ty u &
           typing f g t ty)

val check_term_with_expected_type (f:RT.fstar_top_env) (g:env) (e:term) (t:term)
  : T.Tac (e:term & typing f g e t)

val core_check_term (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (ty:term &
           typing f g t ty)

val core_check_term_with_expected_type (f:RT.fstar_top_env) (g:env) (e:term) (t:term)
  : T.Tac (typing f g e t)

val check_vprop (f:RT.fstar_top_env)
                (g:env)
                (t:term)
  : T.Tac (t:term & tot_typing f g t Tm_VProp)

val check_vprop_with_core (f:RT.fstar_top_env)
                          (g:env)
                          (t:term)
  : T.Tac (tot_typing f g t Tm_VProp)

val get_non_informative_witness (f:RT.fstar_top_env) (g:env) (u:universe) (t:term)
  : T.Tac (non_informative_t f g u t)
