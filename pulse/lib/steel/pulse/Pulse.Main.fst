module Pulse.Main

module T = FStar.Tactics
module R = FStar.Reflection
module RT = FStar.Reflection.Typing
open FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker
open Pulse.Elaborate
open Pulse.Soundness
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer

let main' (t:st_term) (pre:term) (g:RT.fstar_top_env)
  : T.Tac (r:(R.term & R.typ){RT.tot_typing g (fst r) (snd r)})
  = 
    match Pulse.Soundness.Common.check_top_level_environment g with
    | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
    | Some g ->
      if RU.debug_at_level (fstar_env g) "Pulse"
      then (
        T.print (Printf.sprintf "About to check pulse term:\n%s\n" (P.st_term_to_string t))
      );
      let (| pre, ty, pre_typing |) = Pulse.Checker.Pure.check_term g pre in
      if eq_tm ty Tm_VProp
      then let pre_typing : tot_typing g pre Tm_VProp = E pre_typing in
           let (| t, c, t_typing |) = check g t pre pre_typing None in
           let refl_e = elab_st_typing t_typing in
           let refl_t = elab_comp c in
           soundness_lemma g t c t_typing;
           (refl_e, refl_t)
      else fail g (Some t.range) "pulse main: cannot typecheck pre at type vprop"

let main t pre : RT.dsl_tac_t = main' t pre
  
[@@plugin]
let check_pulse (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
  : RT.dsl_tac_t
  = fun env ->
      match Pulse.ASTBuilder.parse_pulse env namespaces module_abbrevs content file_name line col with
      | Inl st_term ->
        main st_term Tm_Emp env
      | Inr (msg, range) ->
        T.fail (Printf.sprintf "%s: %s"
                  (T.range_to_string range)
                  msg)
