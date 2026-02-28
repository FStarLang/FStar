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

module Pulse.Checker.Return

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module RU = Pulse.RuntimeUtils

let check_effect
    (g:env) (e:term) (eff:T.tot_or_ghost)
    (c:option ctag)
: T.Tac (c:ctag & e:term)
= match c, eff with
  | None, T.E_Total -> 
    (| STT_Atomic, e |)
  | None, T.E_Ghost -> 
    (| STT_Ghost, e |)
  | Some STT_Ghost, T.E_Total ->
    (| STT_Atomic, e |)
  | Some STT_Ghost, T.E_Ghost -> 
    (| STT_Ghost, e |)
  | _, T.E_Total -> 
    (| STT_Atomic, e |)
  | _ -> 
    fail g (Some (RU.range_of_term e)) "Expected a total term, but this term has Ghost effect"
 

let check_tot_or_ghost_term (g:env) (e:term) (t:term) (c:option ctag)
: T.Tac (c:ctag & e:term)
= let (| e, eff |) = check_term_at_type g e t in
  match c, eff with
  | None, T.E_Total
  | Some STT_Ghost, T.E_Total
  | _, T.E_Total -> (| STT_Atomic, e |)
  | None, T.E_Ghost
  | Some STT_Ghost, T.E_Ghost -> (| STT_Ghost, e |)
  | _ ->
    fail g (Some (RU.range_of_term e)) "Expected a total term, but this term has Ghost effect"
  
noeq
type result_of_typing (g:env) =
  | R :
    c:ctag ->
    t:term ->
    u:universe ->
    ty:term ->
    unit ->
    unit ->
    result_of_typing g

let compute_tot_or_ghost_term_type_and_u (g:env) (e:term) (c:option ctag)
: T.Tac (result_of_typing g)
= RU.with_error_bound (RU.range_of_term e) fun () -> // stopgap, ideally remove
  let (| t, eff, ty, u |) = compute_term_type_and_u g e in
  let (| c, e |) = check_effect g t eff c in
  R c e u ty () ()

#push-options "--z3rlimit_factor 16 --fuel 0 --ifuel 1 --split_queries no"
#restart-solver
let check_core
  (g:env)
  (ctxt:term)
  (ctxt_typing:unit)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { Tm_Return? st.term })
  (ctag_ctxt:option ctag)
  : T.Tac (checker_result_t g ctxt post_hint) =
  
  let g = push_context "check_return" st.range g in
  let Tm_Return {expected_type; insert_eq=use_eq; term=t} = st.term in
  let return_type
    : option (ty:term & u:universe) =
    match post_hint with
    | PostHint post ->
      assert (g `env_extends` post.g);

      Some (| post.ret_ty, post.u |)
    | _ ->
      match inspect_term expected_type with
      | Tm_Unknown -> (
        match post_hint with
        | NoHint -> None
        | TypeHint expected_type -> 
          let ty, _ = Pulse.Checker.Pure.instantiate_term_implicits g expected_type None false in
          let u = check_universe g ty in
          Some (| ty, u |)
      )
      | _ ->
        let ty, _ = Pulse.Checker.Pure.instantiate_term_implicits g expected_type None false in
        let u = check_universe g ty in
        Some (| ty, u |)
  in
  let R c t u ty uty d : result_of_typing g =
    match return_type with
    | None ->
      compute_tot_or_ghost_term_type_and_u g t ctag_ctxt
    | Some (| ret_ty, u |) ->
      let (| c, t |) = check_tot_or_ghost_term g t ret_ty ctag_ctxt in
      R c t u ret_ty () ()
  in
  let x = fresh g in
  let px = res_ppname, x in
  let post_opened : term =
      match post_hint with
      | PostHint post ->
        // we already checked for the return type
        let post : post_hint_t = post in
        if x `Set.mem` (freevars post.post)
        then fail g None
               ("check_return: unexpected variable clash in return post,\
                 please file a bug report")
        else 
         open_term_nv post.post px
      | _ ->
        let t = check_tot_term (push_binding g x (fst px) ty) tm_emp tm_slprop in
        t
  in
  //if we're inferring a postcondition, then add an equality (if it is non-trivial)
  let use_eq = use_eq || (not (PostHint? post_hint) && not (T.term_eq ty (`unit))) in
  assume (open_term (close_term post_opened x) x == post_opened);
  let post = close_term post_opened x in
  let ret_st = wtag (Some c) (Tm_Return {expected_type=tm_unknown; insert_eq=use_eq; term=t}) in
  let ret_c = comp_return c use_eq u ty t post x in

  let c' = match_comp_res_with_post_hint ret_st ret_c () post_hint in
  Pulse.Checker.Util.debug g "pulse.return" (fun _ -> 
    Printf.sprintf "Return comp is: %s"
      (Pulse.Syntax.Printer.comp_to_string c'));
  prove_post_hint #g
    (try_frame_pre false #g ctxt_typing (|ret_st,c'|) res_ppname)
    post_hint
    st.range
#pop-options

let check
  (g:env)
  (ctxt:term)
  (ctxt_typing:unit)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { Tm_Return? st.term })
  (check:check_t)
: T.Tac (checker_result_t g ctxt post_hint)
= let Tm_Return f = st.term in
  let rebuild (tt: either term st_term) : T.Tac st_term =
    match tt with
    | Inl t -> { st with term = Tm_Return { f with term = t } }
    | Inr st_app -> { st_app with source = st.source }
  in
  match Pulse.Checker.Base.hoist g (Inl f.term) false rebuild with
  | Some tt -> //some elaboration, go back to top
    Pulse.Checker.Util.debug g "pulse.hoist" (fun _ ->
      Printf.sprintf "Hoisted term: %s" (Pulse.Syntax.Printer.st_term_to_string tt)
    );
    check g ctxt ctxt_typing post_hint res_ppname tt
  | None -> (
    match post_hint with
    | PostHint p -> (
      let ctag =
        match ctag_of_effect_annot p.effect_annot with
        | Some c -> c
        | None -> STT_Atomic in
      check_core g ctxt ctxt_typing post_hint res_ppname st (Some ctag)
      
    )
    | _ ->  check_core g ctxt ctxt_typing post_hint res_ppname st None
  )
