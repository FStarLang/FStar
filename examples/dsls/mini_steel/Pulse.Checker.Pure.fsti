module Pulse.Checker.Pure
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Readback
module RTB = FStar.Tactics.Builtins

val check_universe (f0:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (u:universe & universe_of f0 g t u)
  
      
val check_tot_univ (allow_inst:bool) (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (t:term  &
           u:universe &
           ty:term &
           universe_of f g ty u &
           typing f g t ty)

val check_tot (allow_inst:bool) (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (t:term &
           ty:term &
           typing f g t ty)

val check_tot_with_expected_typ (f:RT.fstar_top_env) (g:env) (e:term) (t:term)
  : T.Tac (e:term & typing f g e t)

val check_tot_no_inst (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (ty:term &
           typing f g t ty)

val check_vprop_no_inst (f:RT.fstar_top_env)
                        (g:env)
                        (t:term)
  : T.Tac (tot_typing f g t Tm_VProp)

val check_vprop (f:RT.fstar_top_env)
                (g:env)
                (t:term)
  : T.Tac (t:term & _:tot_typing f g t Tm_VProp)

val get_non_informative_witness (f:RT.fstar_top_env) (g:env) (u:universe) (t:term)
  : T.Tac (non_informative_t f g u t)
