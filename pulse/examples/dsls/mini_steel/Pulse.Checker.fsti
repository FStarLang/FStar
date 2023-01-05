module Pulse.Checker
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing

val readback_universes (us:list R.universe)
  : o:option (list universe) { 
          Some? o ==> List.Tot.map elab_universe (Some?.v o) == us 
    }

val readback_qual (q:R.aqualv)
  : option qualifier
  
val readback_ty (t:R.term)
  : T.Tac (option (ty:pure_term { elab_term ty == Some t }))

val readback_comp (t:R.term)
  : T.Tac (option (c:comp{ elab_comp c == Some t}))

val check_tot (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(ty:pure_term &
              src_typing f g t (C_Tot ty)) { is_pure_term t })
  
type check_t =
  f:RT.fstar_top_env ->
  g:env ->
  t:term ->
  pre:pure_term ->
  pre_typing:tot_typing f g pre Tm_VProp ->
  post_hint:option term ->
  T.Tac (c:pure_comp{C_ST? c ==> comp_pre c == pre} &
         src_typing f g t c)

val check : check_t
