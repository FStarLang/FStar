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

module Pulse.Checker.ST
open FStar.Tactics.V2
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Reflection.Util

module T = FStar.Tactics.V2
module RU = Pulse.RuntimeUtils
module R = FStar.Reflection.V2
module P = Pulse.Syntax.Printer
open Pulse.Checker.Prover
open Pulse.Show

let should_allow_ambiguous (t:term) : T.Tac bool =
  Pulse.Reflection.Util.head_has_attr_string "Pulse.Lib.Core.allow_ambiguous" t

exception UnreachableImplicitNotSolved of unit

let rec solve_unreachable_implicits (g:env) (e:term) : T.Tac unit =
  let pending = RU.scoped_implicits (elab_env g) e in
  T.iter (fun (scope, uv, ty) ->
    let ty = RU.deep_compress_safe ty in
    if not (RU.no_uvars_in_term ty) then () else
    match R.inspect_ln ty with
    | R.Tv_Type _ -> ()
    | _ ->
      // Prove the contradiction in the uvar's creation scope, not the caller's.
      let false_typing, _ = T.with_policy T.ForceSMT (fun () ->
        T.core_check_term_at_type scope tm_l_false (`prop)) in
      let valid, _ =
        match false_typing with
        | Some T.E_Total ->
          T.with_policy T.ForceSMT (fun () -> T.check_prop_validity scope tm_l_false)
        | _ -> None, [] in
      match valid with
      | None -> ()
      | Some _ ->
        let universe, _ = T.with_policy T.ForceSMT (fun () -> T.universe_of scope ty) in
        (match universe with
        | None -> ()
        | Some u ->
          let head = R.pack_ln (R.Tv_UInst
            (R.pack_fv ["FStar"; "Pervasives"; "false_elim"]) [u]) in
          let witness = R.mk_app head [ty, R.Q_Implicit; unit_const, R.Q_Explicit] in
          let checked, _ = T.with_policy T.ForceSMT (fun () ->
            T.core_check_term_at_type scope witness ty) in
          (match checked with
          | Some T.E_Total ->
            (try
              if not (T.with_policy T.ForceSMT (fun () -> T.unify_env scope uv witness))
              then T.raise (UnreachableImplicitNotSolved ())
            with
            | UnreachableImplicitNotSolved _ -> ()
            | ex -> T.raise ex)
          | _ -> ()))
  ) pending;
  let remaining = RU.scoped_implicits (elab_env g) e in
  if Cons? remaining && List.Tot.length remaining < List.Tot.length pending then
    solve_unreachable_implicits g e

open Pulse.PP
#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 3"
let check
  (g:env)
  (ctxt:slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_ST? t.term })
  : T.Tac (checker_result_t g ctxt post_hint) =

  let g = push_context "st" t.range g in
  let post_hint: post_hint_opt g = post_hint in
  let range = t.range in
  let Tm_ST { t=e; args } = t.term in
  if Cons? args then
    fail_doc g (Some t.range) [
      text "Internal error: trailing combinator arguments not lifted in Tm_ST";
      fquotes (pp t)
    ];
  let e, ty, eff = tc_term_phase1 g e in
  match Pulse.Readback.readback_comp ty with
  | None -> fail g (Some range) (Printf.sprintf "readback of %s failed" (show ty))
  | Some (C_Tot _) ->
    let h, a = T.collect_app_ln e in
    let (| _, _, th |) = Pulse.Checker.Pure.compute_term_type g h in
    let open Pulse.PP in
    fail_doc g 
      (Some range)
      [text "Expected an application of a function returning a computation type { stt, stt_ghost, stt_atomic }";
       text "But the application:";
       fquotes (pp e);
       text "is a total term";
       text "Maybe it is not fully applied?"]

  | Some c0 -> (
    let allow_ambiguous = should_allow_ambiguous e in
    let (| g', ctxt', k |) = prove (RU.range_of_term e) g ctxt (comp_pre c0) allow_ambiguous in

    if not (RU.no_uvars_in_term e) then
      solve_unreachable_implicits g' e;
    if not (RU.no_uvars_in_term e) then
      fail_doc g (Some range) [
        text "Unexpected unresolved uvars in the term:";
        fquotes (pp e)
      ];
    if not (RU.no_uvars_in_term ty) then
      fail_doc g (Some range) [
        text "Unexpected unresolved uvars in the type:";
        fquotes (pp ty)
      ];

    // remove spurious beta-redexes
    let e = e |> RU.beta_lax (elab_env g) |> RU.deep_compress in
    let ty = ty |> RU.beta_lax (elab_env g) |> RU.deep_compress in
    assume elab_comp c0 == ty;
    let Some c = Pulse.Readback.readback_comp ty in

    let eff = core_check_term_at_type g' e ty in
    let t = { t with term = Tm_ST { t=e; args=[] }; effect_tag = Some (ctag_of_comp_st c) } in
    if not (eff = T.E_Total) then (
      match c with
      | C_ST _ | C_STDiv _ | C_STAtomic .. ->
        let open Pulse.PP in
        fail_doc g (Some range)
          [text "Application of a stateful or atomic computation cannot have a ghost effect";
          fquotes (pp t);
          text "has computation type";
          fquotes (pp c)]
      | C_STGhost .. ->
        let token = is_non_informative g' c in
        (match token with
         | None ->
           fail g' (Some range)
             (Printf.sprintf "Unexpected informative result for %s" (P.comp_to_string c))
         | Some _ -> ())
    );
 // TODO: thread through prover
      if comp_post c `eq_tm` tm_is_unreachable then
        let framed = checker_result_for_st_typing (k _ (| t, add_frame c ctxt' |)) res_ppname in
        RU.record_stats "prove_post_hint" fun _ -> prove_post_hint framed post_hint range
      else
        // TODO: not sure why we need the type equality check below..
        let c = match_comp_res_with_post_hint t c post_hint in
        let framed = checker_result_for_st_typing (k _ (| t, add_frame c ctxt' |)) res_ppname in
        RU.record_stats "prove_post_hint" fun _ -> prove_post_hint framed post_hint range
  )
#pop-options