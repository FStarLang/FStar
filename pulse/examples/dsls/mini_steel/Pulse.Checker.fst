module Pulse.Checker
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Readback
open Pulse.Checker.Pure
open Pulse.Checker.Framing
open Pulse.Checker.Bind
module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.Builtins

#push-options "--z3rlimit_factor 2"
let replace_equiv_post
  (f:RT.fstar_top_env)
  (g:env)
  (c:pure_comp{stateful_comp c})
  (post_hint:option term)

  : T.Tac (c1:pure_comp { stateful_comp c1 /\ comp_pre c1 == comp_pre c } & st_equiv f g c c1) =

  let {u=u_c;res=res_c;pre=pre_c;post=post_c} = st_comp_of_comp c in
  let x = fresh g in
  let g_post = (x, Inl res_c)::g in

  let pre_c_typing : tot_typing f g pre_c Tm_VProp =
    check_vprop_no_inst f g pre_c in
  let res_c_typing : tot_typing f g res_c (Tm_Type u_c) =
    let (| u, ty |) = check_universe f g res_c in
    if u = u_c
    then ty
    else T.fail "T_Abs: re-typechecking the return type returned different universe" in
  let post_c_opened = open_term post_c x in
  let post_c_typing
    : tot_typing f g_post (open_term post_c x) Tm_VProp
    = check_vprop_no_inst f g_post post_c_opened in

  match post_hint with
  | None ->
    (| c,
       ST_VPropEquiv
         g c c x pre_c_typing res_c_typing post_c_typing
         (VE_Refl _ _)
         (VE_Refl _ _) |)
  | Some post ->
    let post_opened = open_term post x in
    let (| post_opened, post_typing |) = check_vprop f g_post post_opened in
    let post_c_post_eq : vprop_equiv f g_post post_c_opened post_opened =
      check_vprop_equiv f g_post post_c_opened post_opened post_c_typing in

    let st_comp_with_post = {
        u=u_c;
        res=res_c;
        pre=pre_c;
        post=close_term post_opened x
    } in
    let c_with_post = c `with_st_comp` st_comp_with_post in
    assume (open_term (close_term post_opened x) x == post_opened);
    assert (is_pure_term (close_term post_opened x));
    (| c_with_post,
       ST_VPropEquiv
         g c c_with_post x pre_c_typing res_c_typing post_c_typing
         (VE_Refl _ _)
         post_c_post_eq |)
#pop-options

let check_abs
  (f:RT.fstar_top_env)
  (g:env)
  (t:term{Tm_Abs? t})
  (pre:pure_term)
  (pre_typing:tot_typing f g pre Tm_VProp)
  (post_hint:option term)
  (check:check_t)
  : T.Tac (t:term &
           c:pure_comp { stateful_comp c ==> comp_pre c == pre } &
           src_typing f g t c) =
  match t with  
  | Tm_Abs {binder_ty=t;binder_ppname=ppname} qual pre_hint body post_hint ->  (* {pre}  (fun (x:t) -> body) : ? { pre } *)
    let (| t, _, _ |) = check_tot true f g t in //elaborate it first
    let (| u, t_typing |) = check_universe f g t in //then check that its universe ... We could collapse the two calls
    let x = fresh g in
    let g' = (x, Inl t) :: g in
    let pre_opened = open_term pre_hint x in
    match check_tot true f g' pre_opened with
    | (| pre_opened, Tm_VProp, pre_typing |) ->
      let pre = close_term pre_opened x in
      let post =
        match post_hint with
        | None -> None
        | Some post ->
          let post = open_term' post (Tm_Var {nm_ppname="_";nm_index=x}) 1 in
          Some post
      in
      let (| body', c_body, body_typing |) = check f g' (open_term body x) pre_opened (E pre_typing) post in

      let body_closed = close_term body' x in
      assume (open_term body_closed x == body');

      let tt = T_Abs g ppname x qual t u body_closed c_body pre_hint post_hint t_typing body_typing in
      let tres = Tm_Arrow {binder_ty=t;binder_ppname=ppname} qual (close_comp c_body x) in
      (| Tm_Abs {binder_ty=t;binder_ppname=ppname} qual pre_hint body_closed post_hint, 
         C_Tot tres,
         tt |)
    | _ -> T.fail "bad hint"

#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 4"
#push-options "--print_implicits --print_universes --print_full_names"
let rec check' : bool -> check_t =
  fun (allow_inst:bool)
    (f:RT.fstar_top_env)
    (g:env)
    (t:term)
    (pre:pure_term)
    (pre_typing: tot_typing f g pre Tm_VProp)
    (post_hint:option term) ->
  let repack #g #pre #t (x:(c:pure_comp_st { comp_pre c == pre } & src_typing f g t c)) (apply_post_hint:bool)
    : T.Tac (t:term & c:pure_comp { stateful_comp c ==> comp_pre c == pre } & src_typing f g t c) =
    let (| c, d_c |) = x in
    if apply_post_hint && stateful_comp c
    then
      let (| c1, c_c1_eq |) = replace_equiv_post f g c post_hint in
      (| t, c1, T_Equiv _ _ _ _ d_c c_c1_eq |)
    else (| t, c, d_c |)
  in
  match t with
  | Tm_BVar _ -> T.fail "not locally nameless"
  | Tm_Var _
  | Tm_FVar _ 
  | Tm_UInst _ _
  | Tm_Constant _
  | Tm_PureApp _ _ _
  | Tm_Let _ _ _ ->
    let (| t, u, ty, uty, d |) = check_tot_univ allow_inst f g t in
    let c = return_comp u ty t in
    let d = T_Return _ _ _ _ (E d) uty in
    repack (frame_empty pre_typing uty t c d) false

  | Tm_Emp
  | Tm_Pure _
  | Tm_Star _ _ 
  | Tm_ExistsSL _ _
  | Tm_ForallSL _ _
  | Tm_Arrow _ _ _
  | Tm_Type _
  | Tm_VProp
  | Tm_Refine _ _
  | Tm_Inames
  | Tm_EmpInames ->
    let (| t, ty, d_ty |) = check_tot allow_inst f g t in
    (| t, C_Tot ty, d_ty |)

  | Tm_Abs _ _ _ _ _ ->
    check_abs f g t pre pre_typing post_hint (check' true)
  
  | Tm_STApp head qual arg ->
    let (| head, ty_head, dhead |) = check_tot allow_inst f g head in
    begin
    match ty_head with
    | Tm_Arrow {binder_ty=formal;binder_ppname=ppname} bqual comp_typ -> (
      if qual = bqual
      then (
        let (| arg, darg |) = check_tot_with_expected_typ f g arg formal in
        match comp_typ with
        | C_ST res
        | C_STAtomic _ res
        | C_STGhost _ res ->
          // This is a real ST application
          let d = T_STApp g head ppname formal qual comp_typ arg dhead (E darg) in
          opening_pure_comp_with_pure_term comp_typ arg 0;
          repack (try_frame_pre pre_typing d) true
        | C_Tot (Tm_Arrow _  (Some implicit) _) -> 
          let head = Tm_PureApp head qual arg in
          let C_Tot ty_head = open_comp_with comp_typ arg in
          //Some implicits to follow
          let t = Pulse.Checker.Inference.infer head ty_head pre in
          check' false f g t pre pre_typing post_hint

        | _ ->
          T.fail "Unexpected head type in stateful application"
      )
      else T.fail "Unexpected qualifier"
    )
    
    | _ -> T.fail (Printf.sprintf "Unexpected head type in impure application: %s" (P.term_to_string ty_head))
    end

  | Tm_Bind _ _ ->
    check_bind f g t pre pre_typing post_hint (check' true)
    
  | Tm_If _ _ _ ->
    T.fail "Not handling if yet"

  | Tm_UVar _ ->
    T.fail "Unexpected Tm_Uvar in check"
#pop-options

let check = check' true
