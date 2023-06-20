module Pulse.Checker.Pure
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Readback
module RTB = FStar.Tactics.Builtins
module RU = Pulse.RuntimeUtils

let push_context (ctx:string) (r:range) (g:env) : (g':env { g == g' })
  = push_context g ctx r

val instantiate_term_implicits (g:env) (t:term)
  : T.Tac (term & term)

val check_universe (g:env) (t:term)
  : T.Tac (u:universe & universe_of g t u)

val check_term (g:env) (t:term)
  : T.Tac (t:term &
           ty:term &
           typing g t ty)

val check_term_and_type (g:env) (t:term)
  : T.Tac (t:term  &
           u:universe &
           ty:term &
           universe_of g ty u &
           typing g t ty)

val check_term_with_expected_type (g:env) (e:term) (t:term)
  : T.Tac (e:term & typing g e t)

val core_check_term (g:env) (t:term)
  : T.Tac (ty:term &
           typing g t ty)

val core_check_term_with_expected_type (g:env) (e:term) (t:term)
  : T.Tac (typing g e t)

val check_vprop (g:env)
                (t:term)
  : T.Tac (t:term & tot_typing g t tm_vprop)

val check_vprop_with_core (g:env)
                          (t:term)
  : T.Tac (tot_typing g t tm_vprop)

val get_non_informative_witness (g:env) (u:universe) (t:term)
  : T.Tac (non_informative_t g u t)

val check_prop_validity (g:env) (p:term) (_:tot_typing g p tm_prop)
  : T.Tac (Pulse.Typing.prop_validity g p)
