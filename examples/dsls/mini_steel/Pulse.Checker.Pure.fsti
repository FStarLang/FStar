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
  : T.Tac (_:(u:universe & universe_of f0 g t u) { is_pure_term t })
  
      
val check_tot_univ (allow_inst:bool) (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(t:pure_term  &
              u:universe &
              ty:pure_term &
              universe_of f g ty u &
              src_typing f g t (C_Tot ty)) { is_pure_term t } )

val check_tot (allow_inst:bool) (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(t:pure_term &
              ty:pure_term &
              src_typing f g t (C_Tot ty)) { is_pure_term t })

val check_tot_with_expected_typ (f:RT.fstar_top_env) (g:env) (e:term) (t:pure_term)
  : T.Tac (_:(e:pure_term & src_typing f g e (C_Tot t)){is_pure_term e})


val check_tot_no_inst (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(ty:pure_term &
              src_typing f g t (C_Tot ty)) { is_pure_term t })

val check_vprop_no_inst (f:RT.fstar_top_env)
                        (g:env)
                        (t:term)
  : T.Tac (_:tot_typing f g t Tm_VProp{is_pure_term t})

val check_vprop (f:RT.fstar_top_env)
                (g:env)
                (t:term)
  : T.Tac (t:pure_term & _:tot_typing f g t Tm_VProp{is_pure_term t})
