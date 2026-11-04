(*
   Copyright 2026 Microsoft Research

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

module Pulse.Checker.Goto

module T = FStar.Tactics.V2
module R = FStar.Reflection.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

let check'
  (g:env)
  (pre:term)
  (post_hint:post_hint_opt g { PostHint? post_hint })
  (res_ppname:ppname)
  (t:st_term { Tm_Goto? t.term })
  (native_raise:option (term & term))
: T.Tac (checker_result_t g pre post_hint)
= let rng = t.range in
  let Tm_Goto { lbl; arg } = t.term in
  let PostHint ph = post_hint in
  match R.inspect_ln lbl with
  | R.Tv_Var v ->
    let v = (R.inspect_namedv v).uniq in
    (match lookup_goto g v with
    | Some (lbln, lbl_c) ->
      let arg = check_tot_term g arg (comp_res lbl_c) in
      let sc = {
        u = ph.u;
        res = ph.ret_ty;
        pre = open_term' (comp_pre lbl_c) arg 0;
        post = ph.post
      } in
      // A goto never returns (its post is `is_unreachable`), so its local
      // effect can follow the surrounding context's effect annotation rather
      // than the label's. This lets a `return` compose in a plain (STT) block
      // even when the enclosing function's return label is divergent, and vice
      // versa. Extraction uses the label's comp (see Pulse.Extract.Main), so
      // this choice does not affect the emitted code.
      let c' : comp_st =
        match ph.effect_annot with
        | EffectAnnotSTT -> C_ST sc
        | EffectAnnotSTTDiv -> C_STDiv sc
        | _ -> with_st_comp lbl_c sc
      in
      // The lexical goto protocol above remains the proof obligation. Only
      // after checking its payload do native raises acquire runtime syntax.
      let runtime =
        match native_raise with
        | None -> Tm_Goto { lbl = term_of_nvar (lbln, v); arg }
        | Some (exn_ty, payload) ->
          Tm_NativeRaise { exn_ty; result_ty=comp_res c'; arg=payload }
      in
      let t = wtag (Some (ctag_of_comp_st c')) runtime in
      let c' = match_comp_res_with_post_hint t c' post_hint in
      // lookup_goto has added the BindingPost obligations for local/defer scopes
      // crossed by this jump; substituting arg selects the destination's exit
      // protocol (e.g. exit_post q r (Raised e) = r e). Transfer to that complete
      // obligation EXACTLY. Ordinary precondition framing would retain resources
      // for a continuation which never runs, silently leaking a caller's frame.
      // This applies to every goto, including return/break/continue, not just
      // raises: an early return from inside a try also bypasses its continuation.
      let (| g', k |) = prove_exact rng g pre (comp_pre c') in
      prove_post_hint #g
        (checker_result_for_st_typing (k NoHint (|t,c'|)) res_ppname)
        post_hint
        rng
    | None ->
      fail g (Some t.range) "Unknown goto label")
  | _ ->
    fail g (Some t.range) "Goto label is not a variable"

let check_with
  (g:env)
  (pre:term)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_Goto? t.term })
  (native_raise:option (term & term))
: T.Tac (checker_result_t g pre post_hint)
= match post_hint with
  | NoHint ->
    let post_hint' = intro_post_hint g EffectAnnotSTT None tm_is_unreachable in
    let res = check' g pre (PostHint post_hint') res_ppname t native_raise in
    retype_checker_result _ res
  | TypeHint ty ->
    let post_hint' = intro_post_hint g EffectAnnotSTT (Some ty) tm_is_unreachable in
    let res = check' g pre (PostHint post_hint') res_ppname t native_raise in
    retype_checker_result _ res
  | PostHint post ->
    check' g pre post_hint res_ppname t native_raise

let check g pre post_hint res_ppname t =
  check_with g pre post_hint res_ppname t None

let check_native_raise g pre post_hint res_ppname t exn_ty payload =
  check_with g pre post_hint res_ppname t (Some (exn_ty, payload))
