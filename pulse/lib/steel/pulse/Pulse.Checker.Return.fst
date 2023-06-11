module Pulse.Checker.Return

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common

module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV

let check_return
  (allow_inst:bool)
  (g:env)
  (st:st_term{Tm_Return? st.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint) =
  let g = push_context "check_return" st.range g in
  let Tm_Return {ctag=c; insert_eq=use_eq; term=t} = st.term in
  let (| t, u, ty, uty, d |) :
    t:term &
    u:universe &
    ty:term &
    universe_of g ty u &
    typing g t ty =
    match post_hint with
    | None -> check_term_and_type g t
    | Some post ->
      let (| t, d |) = check_term_with_expected_type g t post.ret_ty in
      assert (g `env_extends` post.g);
      let ty_typing : universe_of post.g post.ret_ty post.u =
        post.ty_typing in
      // weakening of post.g to g
      let ty_typing : universe_of g post.ret_ty post.u = magic () in
      (| t, post.u, post.ret_ty, ty_typing, d |)
  in
  let x = fresh g in
  let px = v_as_nv x in
  let (| post_opened, post_typing |) : t:term & tot_typing (push_binding g x (fst px) ty)  t Tm_VProp =
      match post_hint with
      | None -> 
        let (| t, ty |) = check_term_with_expected_type (push_binding g x (fst px) ty) Tm_Emp Tm_VProp in
        (| t, E ty |)
        
      | Some post ->
        // we already checked for the return type
        let post : post_hint_t = post in
        if x `Set.mem` (freevars post.post)
        then fail g None "Unexpected variable clash in return"
        else 
         let ty_rec = post_hint_typing g post x in
         (| open_term_nv post.post px, ty_rec.post_typing |)
  in
  assume (open_term (close_term post_opened x) x == post_opened);
  let post = close_term post_opened x in
  let d = T_Return g c use_eq u ty t post x uty (E d) post_typing in
  repack (Pulse.Checker.Common.try_frame_pre pre_typing d) post_hint
