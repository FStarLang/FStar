module Pulse.Checker.WithLocal

module T = FStar.Tactics
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common

module FV = Pulse.Typing.FV

#push-options "--z3rlimit_factor 4"
let extend_post_hint_for_local (g:env) (p:post_hint_for_env g)
                               (init_t:term) (x:var)
  : post_hint_for_env (extend x (Inl init_t) g)
  = { p with post = comp_withlocal_body_post p.post init_t (null_var x);
             post_typing = admit() } //star typing intro

let with_local_pre_typing (#g:env) (#pre:term) (pre_typing:tot_typing g pre Tm_VProp)
                          (init_t:term) (x:var) (i:term)
  : tot_typing (extend x (Inl (mk_ref init_t)) g)
               (comp_withlocal_body_pre pre init_t (null_var x) i)
               Tm_VProp
  = admit()


  
let check_withlocal
  (allow_inst:bool)
  (g:env)
  (t:st_term{Tm_WithLocal? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  (check':bool -> check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  let g = push_context "check_withlocal" g in
  let wr t0 = { term = t0; range = t.range } in
  let Tm_WithLocal {initializer=init; body} = t.term in
  let (| init, init_u, init_t, init_t_typing, init_typing |) =
    check_term_and_type g init in
  if eq_univ init_u u0
  then let x = fresh g in
       let px = v_as_nv x in
       if x `Set.mem` freevars_st body
       then T.fail "withlocal: x is free in body"
       else
         let x_tm = null_var x in
         let g_extended = extend x (Inl (mk_ref init_t)) g in
         let body_pre = comp_withlocal_body_pre pre init_t x_tm init in
         let body_pre_typing = with_local_pre_typing pre_typing init_t x init in
         // elaborating this post here,
         //   so that later we can check the computed post to be equal to this one
         let post : post_hint_for_env g =
           // let post =
             match post_hint with
             | Some post -> post
             | None -> T.fail "withlocal: no post_hint!"
         in
         if x `Set.mem` freevars post.post
         then T.fail "Unexpected name clash in with_local"
         else (
           let body_post = extend_post_hint_for_local g post init_t x in
           let (| opened_body, c_body, body_typing |) =
             check' allow_inst g_extended (open_st_term_nv body px) body_pre body_pre_typing (Some body_post) in
           //
           // Checking post equality here to match the typing rule
           // 
           if not (C_ST? c_body)
           then T.fail "withlocal: body is not stt or postcondition mismatch"
           else let body = close_st_term opened_body x in
                assume (open_st_term (close_st_term opened_body x) x == opened_body);
                let c = C_ST {u=comp_u c_body;res=comp_res c_body;pre;post=post.post} in
                let c_typing =
                    let post_typing_rec = post_hint_typing g post x in
                    intro_comp_typing g c pre_typing post_typing_rec.ty_typing x post_typing_rec.post_typing
                in
                let d = T_WithLocal g init body init_t c x
                                    (E init_typing)
                                    init_t_typing
                                    c_typing
                                    body_typing 
                in
                (| _, _, d |)
         )
  else T.fail "withlocal: init type is not universe zero"
#pop-options
