module Pulse.Checker.Return

module T = FStar.Tactics
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
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c) =
  let g = push_context "check_return" g in
  let Tm_Return {ctag=c; insert_eq=use_eq; term=t} = st.term in
  let (| t, u, ty, uty, d |) = check_term_and_type g t in
  let x = fresh g in
  let px = v_as_nv x in
  let (| post_opened, post_typing |) : t:term & tot_typing (extend x (Inl ty) g)  t Tm_VProp =
      match post_hint with
      | None -> 
        let (| t, ty |) = check_term_with_expected_type (extend x (Inl ty) g) Tm_Emp Tm_VProp in
        (| t, E ty |)
        
      | Some post ->
        let post : post_hint_t = post in
        if not (eq_tm post.ret_ty ty)
        then T.fail (Printf.sprintf "(%s) Expected return type %s, got %s\n"
                                    (T.range_to_string st.range)
                                    (P.term_to_string post.ret_ty)
                                    (P.term_to_string ty))
        else if x `Set.mem` (freevars post.post)
        then T.fail "Unexpected variable clash in return"
        else 
         let ty_rec = post_hint_typing g post x in
         (| open_term_nv post.post px, ty_rec.post_typing |)
  in
  assume (open_term (close_term post_opened x) x == post_opened);
  let post = close_term post_opened x in
  let d = T_Return g c use_eq u ty t post x uty (E d) post_typing in
  repack (Pulse.Checker.Common.try_frame_pre pre_typing d) post_hint true
