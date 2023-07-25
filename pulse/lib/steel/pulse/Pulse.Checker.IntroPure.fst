module Pulse.Checker.IntroPure

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer

let check_prop (g:env) (p:term) 
  : T.Tac (p:term & tot_typing g p tm_prop) =
  
  let p0 = p in
  let (| p, p_typing |) = Pulse.Checker.Pure.check_vprop g (tm_pure p) in
  match p.t with
  | Tm_Pure pp ->
    let prop_typing = Pulse.Typing.Metatheory.pure_typing_inversion #_ #pp p_typing in
    (| pp, prop_typing |)
  | _ ->
    fail g None
      (Printf.sprintf "Impossible: check_intro_pure: checking a pure vprop %s returned a non-pure vprop %s,\
                       please file a bug-report"
         (P.term_to_string (tm_pure p0))
         (P.term_to_string p))

let check_prop_validity (g:env) (p:term) (typing:tot_typing g p tm_prop): T.Tac (prop_validity g p) =
    Pulse.Checker.Pure.check_prop_validity g p typing

let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (t:st_term { Tm_IntroPure? t.term })

  : T.Tac (checker_result_t g pre post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_intro_pure" t.range in

  let Tm_IntroPure { p } = t.term in
  let (| p, p_typing |) = check_prop g p in
  let pv = check_prop_validity g p p_typing in
  let st_typing = T_IntroPure _ _ p_typing pv in
  prove_post_hint (try_frame_pre pre_typing st_typing) post_hint t.range
