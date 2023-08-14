module Pulse.Checker.Return

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module Metatheory = Pulse.Typing.Metatheory

let check_core
  (g:env)
  (ctxt:term)
  (ctxt_typing:tot_typing g ctxt tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { Tm_Return? st.term })
  : T.Tac (checker_result_t g ctxt post_hint) =
  
  let g = push_context "check_return" st.range g in
  let Tm_Return {ctag=c; insert_eq=use_eq; term=t} = st.term in
  let (| t, u, ty, uty, d |) :
    t:term &
    u:universe &
    ty:term &
    universe_of g ty u &
    tot_typing g t ty =
    match post_hint with
    | None -> check_tot_term_and_type g t
    | Some post ->
      let (| t, d |) = check_tot_term_with_expected_type g t post.ret_ty in
      assert (g `env_extends` post.g);
      let ty_typing : universe_of post.g post.ret_ty post.u =
        post.ty_typing in
      let ty_typing : universe_of g post.ret_ty post.u =
        Metatheory.tot_typing_weakening_standard post.g post.ty_typing g in
      (| t, post.u, post.ret_ty, ty_typing, d |)
  in
  
  let x = fresh g in
  let px = res_ppname, x in
  let (| post_opened, post_typing |) : t:term & tot_typing (push_binding g x (fst px) ty)  t tm_vprop =
      match post_hint with
      | None -> 
        let (| t, ty |) = check_tot_term_with_expected_type (push_binding g x (fst px) ty) tm_emp tm_vprop in
        (| t, ty |)
        
      | Some post ->
        // we already checked for the return type
        let post : post_hint_t = post in
        if x `Set.mem` (freevars post.post)
        then fail g None
               ("check_return: unexpected variable clash in return post,\
                 please file a bug report")
        else 
         let ty_rec = post_hint_typing g post x in
         (| open_term_nv post.post px, ty_rec.post_typing |)
  in
  assume (open_term (close_term post_opened x) x == post_opened);
  let post = close_term post_opened x in
  let d = T_Return g c use_eq u ty t post x uty d post_typing in
  prove_post_hint (try_frame_pre ctxt_typing d res_ppname) post_hint t.range

let check
  (g:env)
  (ctxt:term)
  (ctxt_typing:tot_typing g ctxt tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { Tm_Return? st.term })
  : T.Tac (checker_result_t g ctxt post_hint)
  = match post_hint, st.term with
    | Some { ctag_hint = Some ct }, Tm_Return f ->
      if ct = f.ctag
      then check_core g ctxt ctxt_typing post_hint res_ppname st
      else let st = { st with term = Tm_Return { f with ctag=ct }} in
           check_core g ctxt ctxt_typing post_hint res_ppname st
    | _ ->  check_core g ctxt ctxt_typing post_hint res_ppname st
