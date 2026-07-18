(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Checker.IntroPure

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer

let check_prop (g:env) (p:term) 
  : T.Tac term =
  
  let p0 = p in
  let p = Pulse.Checker.Pure.check_slprop g (tm_pure p) in
  match inspect_term p with
  | Tm_Pure pp ->
    let prop_typing = () in
    pp
  | _ ->
    fail g None
      (Printf.sprintf "Impossible: check_intro_pure: checking a pure slprop %s returned a non-pure slprop %s,\
                       please file a bug-report"
         (P.term_to_string (tm_pure p0))
         (P.term_to_string p))

let check_prop_validity (g:env) (p:term): T.Tac (prop_validity g p) =
    Pulse.Checker.Pure.check_prop_validity g p

let check
  (g:env)
  (pre:term)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_IntroPure? t.term })

  : T.Tac (checker_result_t g pre post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_intro_pure" t.range in

  let Tm_IntroPure { p } = t.term in
  let p = check_prop g p in

  let pv = check_prop_validity g p in
  let intro_st = wtag (Some STT_Ghost) (Tm_IntroPure { p }) in
  let intro_c = C_STGhost tm_emp_inames { u=u0; res=tm_unit; pre=tm_emp; post=tm_pure p } in

  let c = match_comp_res_with_post_hint intro_st intro_c post_hint in
  prove_post_hint (try_frame_pre false (|intro_st,c|) res_ppname) post_hint t.range
