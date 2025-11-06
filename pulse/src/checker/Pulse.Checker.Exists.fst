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

module Pulse.Checker.Exists

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base

open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV

module Metatheory = Pulse.Typing.Metatheory

let slprop_as_list_typing (#g:env) (#p:term)
  (t:tot_typing g p tm_slprop)
  (x:term { List.Tot.memP x (slprop_as_list p) })
  : tot_typing g x tm_slprop
  = assume false; t

let terms_to_string (t:list term)
  : T.Tac string 
  = String.concat "\n" (T.map Pulse.Syntax.Printer.term_to_string t)

#push-options "--z3rlimit_factor 8 --fuel 0 --ifuel 1"
#restart-solver
let check_elim_exists
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_ElimExists? t.term})
  : T.Tac (checker_result_t g pre post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_elim_exists" t.range in

  let Tm_ElimExists { p = t } = t.term in
  let t_rng = Pulse.RuntimeUtils.range_of_term t in
  let (| t, t_typing |) : (t:term & tot_typing g t tm_slprop ) = 
    match inspect_term t with
    | Tm_Unknown -> (
      //There should be exactly one exists_ slprop in the context and we eliminate it      
      let ts = slprop_as_list pre in
      let exist_tms = List.Tot.Base.filter #term (fun t -> match inspect_term t with
                                                           | Tm_ExistsSL _ _ _ -> true
                                                           | _ -> false) ts in
      match exist_tms with
      | [one] -> 
        assume (one `List.Tot.memP` ts);
        (| one, slprop_as_list_typing pre_typing one |) //shouldn't need to check this again
      | _ -> 
        fail g (Some t_rng)
          (Printf.sprintf "Could not decide which exists term to eliminate: choices are\n%s"
             (terms_to_string exist_tms))
      )
    | _ ->
      let t, _ = instantiate_term_implicits g t None false in
      check_slprop g t
  in

  let tv = inspect_term t in
  if not (Tm_ExistsSL? tv)
  then fail g (Some t_rng)
         (Printf.sprintf "check_elim_exists: elim_exists argument %s not an existential"
            (P.term_to_string t));

  let Tm_ExistsSL u { binder_ty=ty } p = tv in

  let (| u', ty_typing |) = universe_of_well_typed_term g ty in
  if eq_univ u u'
  then let x = fresh g in
       let d = T_ElimExists g u ty p x ty_typing t_typing in
       let (|_,d|) = match_comp_res_with_post_hint d post_hint in
       prove_post_hint (try_frame_pre false pre_typing (|_,_,d|) res_ppname) post_hint t_rng
  else fail g (Some t_rng)
         (Printf.sprintf "check_elim_exists: universe checking failed, computed %s, expected %s"
            (P.univ_to_string u') (P.univ_to_string u))
#pop-options

#push-options "--z3rlimit_factor 8 --fuel 2 --ifuel 1"
#restart-solver
let check_intro_exists
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { intro_exists_witness_singleton st })
  (slprop_typing: option (tot_typing g (intro_exists_slprop st) tm_slprop))
  : T.Tac (checker_result_t g pre post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_intro_exists_non_erased" st.range in

  let Tm_IntroExists { p=t; witnesses=[witness] } = st.term in
  let (| t, t_typing |) =
    match slprop_typing with
    | Some typing -> (| t, typing |)
    | _ -> check_slprop g t
  in

  let tv = inspect_term t in
  if not (Tm_ExistsSL? tv)
  then fail g (Some st.range)
         (Printf.sprintf "check_intro_exists_non_erased: slprop %s is not an existential"
            (P.term_to_string t));

  let Tm_ExistsSL u b p = tv in

  Pulse.Typing.FV.tot_typing_freevars t_typing;
  let x = fresh g in
  let ty_typing, _ = Metatheory.tm_exists_inversion #g #u #b.binder_ty #p t_typing x in
  let (| witness, witness_typing |) = 
    check_term g witness T.E_Ghost b.binder_ty in
  let d = T_IntroExists g u b p witness ty_typing t_typing witness_typing in
  let (| c, d |) : (c:_ & st_typing g _ c) = (| _, d |) in
  let (| c, d |) = match_comp_res_with_post_hint d post_hint in
  prove_post_hint (try_frame_pre false pre_typing (|_,_,d|) res_ppname)
                  post_hint
                  (Pulse.RuntimeUtils.range_of_term t)
#pop-options
