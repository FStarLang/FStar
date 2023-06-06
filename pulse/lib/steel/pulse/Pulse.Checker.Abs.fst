module Pulse.Checker.Abs

module T = FStar.Tactics
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common

module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV

#push-options "--z3rlimit_factor 2"
let check_abs
  (g:env)
  (t:st_term{Tm_Abs? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  if Some? post_hint then T.fail "Unexpected post-condition annotation from context for an abstraction" else 
  match t.term with  
  | Tm_Abs { b = {binder_ty=t;binder_ppname=ppname}; q=qual; pre=pre_hint; body; ret_ty; post=post_hint_body } ->
    (*  (fun (x:t) -> {pre_hint} body : t { post_hint } *)
    let (| t, _, _ |) = check_term g t in //elaborate it first
    let (| u, t_typing |) = check_universe g t in //then check that its universe ... We could collapse the two calls
    let x = fresh g in
    let px = ppname, x in
    let g' = extend x (Inl t) g in
    let pre_opened = 
      match pre_hint with
      | None -> T.fail "Cannot typecheck an function without a precondition"
      | Some pre_hint -> open_term_nv pre_hint px in
    match check_term g' pre_opened with
    | (| pre_opened, Tm_VProp, pre_typing |) ->
      let pre = close_term pre_opened x in
      let var = tm_var {nm_ppname=RT.pp_name_default;nm_index=x;nm_range=Range.range_0} in
      let ret_ty = open_term_opt' ret_ty var 0 in
      let post_hint_body = open_term_opt' post_hint_body var 1 in
      let post =
        match post_hint_body with
        | None -> None
        | Some post ->
          let post_hint_typing : post_hint_t = Pulse.Checker.Common.intro_post_hint (push_context "post_hint_typing" g') ret_ty post in
          Some post_hint_typing
      in
      let (| body', c_body, body_typing |) = check g' (open_st_term_nv body px) pre_opened (E pre_typing) post in
      FV.st_typing_freevars body_typing;
      let body_closed = close_st_term body' x in
      assume (open_st_term body_closed x == body');
      let b = {binder_ty=t;binder_ppname=ppname} in
      let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
      let tres = tm_arrow {binder_ty=t;binder_ppname=ppname} qual (close_comp c_body x) in
      (| _,
         C_Tot tres,
         tt |)
    | _ -> T.fail "bad hint"
