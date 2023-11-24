module Pulse.Checker.WithLocalArray

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module RU = Pulse.Reflection.Util

let extend_post_hint
  (g:env)
  (p:post_hint_for_env g)
  (init_t:term)
  (x:var { ~ (Set.mem x (dom g)) })
  : post_hint_for_env (push_binding g x ppname_default init_t)
  = { p with post = comp_withlocal_array_body_post p.post init_t (null_var x);
             post_typing = admit() } //star typing intro

let with_local_array_pre_typing (#g:env) (#pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (init_t:term)
  (init:term)
  (len:term)
  (init_typing:tot_typing g init init_t)
  (len_typing:tot_typing g len tm_szt)
  (x:var { ~ (Set.mem x (dom g)) })
  : tot_typing (push_binding g x ppname_default (mk_array init_t))
               (comp_withlocal_array_body_pre pre init_t (null_var x) init len)
               tm_vprop
  = admit()

let is_annotated_type_array (t:term) : option term =
  match is_pure_app t with
  | Some (head, None, a) ->
    (match is_fvar head with
     | Some (l, _) ->
       if l = RU.array_lid
       then Some a
       else None
     | _ -> None 
    )

  | _ -> None

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_WithLocalArray? t.term })
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context "check_withlocal_array" t.range g in
  let Tm_WithLocalArray {binder; initializer; length; body} = t.term in
  let (| init, init_u, init_t, init_t_typing, init_typing |) =
    (* Check against annotation if any *)
    let ty = binder.binder_ty in
    match ty.t with
    | Tm_Unknown -> compute_tot_term_type_and_u g initializer
    | _ ->
      match is_annotated_type_array ty with
      | None ->
        fail g (Some ty.range)
          (Printf.sprintf "expected annotated type to be an array, found: %s"
             (P.term_to_string ty))
      | Some ty ->
        let (| u, ty_typing |) = check_universe g ty in
        let (| init, init_typing |) =
          check_term g initializer T.E_Total ty in
        let ty_typing : universe_of g ty u = ty_typing in
        let init_typing : typing g init T.E_Total ty = init_typing in
        (| init, u, ty, ty_typing, init_typing |)
        <: (t:term & u:universe & ty:term & universe_of g ty u & tot_typing g t ty)
        (* ^ Need this annotation *)
  in
  let (| len, len_typing |) =
    check_tot_term g length tm_szt in
  if eq_univ init_u u0
  then
    let x = fresh g in
    let px = binder.binder_ppname, x in
    if x `Set.mem` freevars_st body
    then fail g
              (Some body.range)
              (Printf.sprintf "withlocalarray: %s is free in body"
                 (T.unseal binder.binder_ppname.name))
    else
      let x_tm = term_of_nvar px in
      let g_extended = push_binding g x binder.binder_ppname (mk_array init_t) in
      let body_pre = comp_withlocal_array_body_pre pre init_t x_tm init len in
      let body_pre_typing =
        with_local_array_pre_typing pre_typing init_t init len init_typing len_typing x in
      // elaborating this post here,
      //   so that later we can check the computed post to be equal to this one
      let post : post_hint_for_env g =
        match post_hint with
        | Some post -> post
        | None ->
          fail g None "Allocating a mutable local array expects an annotated post-condition"
      in
      if x `Set.mem` freevars post.post
      then fail g None "Impossible! check_withlocal: unexpected name clash in with_local,\
                        please file a bug-report"
      else
        let body_post = extend_post_hint g post init_t x in
        let (| opened_body, c_body, body_typing |) =
          let r =
            check g_extended body_pre body_pre_typing (Some body_post) binder.binder_ppname (open_st_term_nv body px) in
          apply_checker_result_k r binder.binder_ppname in

        if not (C_ST? c_body)
        then fail g (Some body.range)
               (Printf.sprintf "check_withlocalarray: body computation type %s is not ST"
                  (P.comp_to_string c_body))
        else
          let body = close_st_term opened_body x in
          assume (open_st_term (close_st_term opened_body x) x == opened_body);
          let c = C_ST {u=comp_u c_body;res=comp_res c_body;pre;post=post.post} in
          let c_typing =
            let post_typing_rec = post_hint_typing g post x in
            intro_comp_typing g c pre_typing post_typing_rec.ty_typing x post_typing_rec.post_typing
          in
          let d = T_WithLocalArray g binder.binder_ppname init len body init_t c x
            init_typing
            len_typing
            init_t_typing
            c_typing
            body_typing in
          checker_result_for_st_typing (| _, _, d |) res_ppname

  else fail g (Some t.range)
         (Printf.sprintf "check_withlocalarray: allocating a local variable: type %s is not universe zero (computed %s)"
            (P.term_to_string init)
            (P.univ_to_string init_u))
