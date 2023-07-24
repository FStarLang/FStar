module Pulse.Checker.WithLocal

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base

module T = FStar.Tactics.V2

let extend_post_hint_for_local (g:env) (p:post_hint_for_env g)
                               (init_t:term) (x:var { ~ (Set.mem x (dom g)) })
  : post_hint_for_env (push_binding g x ppname_default init_t)
  = { p with post = comp_withlocal_body_post p.post init_t (null_var x);
             post_typing = admit() } //star typing intro

let with_local_pre_typing (#g:env) (#pre:term) (pre_typing:tot_typing g pre tm_vprop)
                          (init_t:term) (x:var { ~ (Set.mem x (dom g)) }) (i:term)
  : tot_typing (push_binding g x ppname_default (mk_ref init_t))
               (comp_withlocal_body_pre pre init_t (null_var x) i)
               tm_vprop
  = admit()

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (t:st_term { Tm_WithLocal? t.term })
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context "check_withlocal" t.range g in
  let wr t0 = { term = t0; range = t.range } in
  let Tm_WithLocal {binder; initializer=init; body} = t.term in
  let (| init, init_u, init_t, init_t_typing, init_typing |) =
    check_term_and_type g init in
  if eq_univ init_u u0
  then
    let x = fresh g in
    let px = binder.binder_ppname, x in
    if x `Set.mem` freevars_st body
    then fail g (Some body.range) (Printf.sprintf "withlocal: %s is free in body" (T.unseal binder.binder_ppname.name))
    else
      let x_tm = term_of_nvar px in
      let g_extended = push_binding g x binder.binder_ppname (mk_ref init_t) in
      let body_pre = comp_withlocal_body_pre pre init_t x_tm init in
      let body_pre_typing = with_local_pre_typing pre_typing init_t x init in
      // elaborating this post here,
      //   so that later we can check the computed post to be equal to this one
      let post : post_hint_for_env g =
        match post_hint with
        | Some post -> post
        | None -> fail g None "Allocating a mutable local variable expects an annotated post-condition"
      in
      if x `Set.mem` freevars post.post
      then fail g None "Unexpected name clash in with_local"
      else
        let body_post = extend_post_hint_for_local g post init_t x in
        let (| opened_body, c_body, body_typing |) =
          let r = check g_extended body_pre body_pre_typing (Some body_post) (open_st_term_nv body px) in
          apply_checker_result_k r in
        //
        // Checking post equality here to match the typing rule
        // 
        if not (C_ST? c_body)
        then fail g (Some body.range) "withlocal: body is not stt or postcondition mismatch"
        else
          let body = close_st_term opened_body x in
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
            body_typing in
          checker_result_for_st_typing (| _, _, d |)

  else fail g None "Allocating a local variable: init type is not universe zero"
