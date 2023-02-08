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
         (VE_Refl _ _ _)
         (VE_Refl _ _ _) |)
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
         (VE_Refl _ _ _)
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

let has_pure_vprops (pre:pure_term) = L.existsb Tm_Pure? (vprop_as_list pre)

let maybe_add_elim_pure (pre:pure_term) (t:term) : T.Tac (bool & term) =
  let pure_props =
    L.flatten (L.map (fun (t:pure_term) ->
                      match t with
                      | Tm_Pure p -> [p]
                      | _ -> []) (vprop_as_list pre)) in

  if L.length pure_props = 0
  then false, t
  else
    true,
    L.fold_left (fun t (p:term) ->
      let elim_pure_tm = Tm_STApp (Tm_FVar (mk_steel_wrapper_lid "elim_pure")) None p in
      Tm_Bind elim_pure_tm t) t pure_props

#push-options "--z3rlimit_factor 10"
let rec combine_if_branches (f:RT.fstar_top_env)
  (g_then:env)
  (e_then:term)
  (c_then:pure_comp_st)
  (e_then_typing:src_typing f g_then e_then c_then)
  (g_else:env)
  (e_else:term)
  (c_else:pure_comp_st)
  (e_else_typing:src_typing f g_else e_else c_else)
  : T.TacH (c:pure_comp_st{comp_pre c == comp_pre c_then} &
            src_typing f g_then e_then c &
            src_typing f g_else e_else c)
           (requires fun _ ->
              comp_pre c_then == comp_pre c_else)
           (ensures fun _ _ -> True) =

  if st_comp_of_comp c_then = st_comp_of_comp c_else
  then begin
    match c_then, c_else with
    | C_ST _, C_ST _ -> (| c_then, e_then_typing, e_else_typing |)
    | C_STAtomic inames1 _, C_STAtomic inames2 _
    | C_STGhost inames1 _, C_STGhost inames2 _ ->
      if inames1 = inames2
      then (| c_then, e_then_typing, e_else_typing |)
      else T.fail "Cannot combine then and else branches (different inames)"
    | C_ST _, C_STAtomic inames _ ->
      if inames = Tm_EmpInames
      then begin
        let e_else_typing =
          T_Lift g_else e_else c_else c_then e_else_typing
            (Lift_STAtomic_ST g_else c_else) in
        (| c_then, e_then_typing, e_else_typing |)
      end
      else T.fail "Cannot lift STAtomic else branch to match then"
    | C_STAtomic inames _, C_ST _ ->
      if inames = Tm_EmpInames
      then begin
        let e_then_typing =
          T_Lift g_then e_then c_then c_else e_then_typing
            (Lift_STAtomic_ST g_then c_then) in
        (| c_else, e_then_typing, e_else_typing |)
      end
      else T.fail "Cannot lift STAtomic else branch to match then"
    | C_STGhost _ _, _ ->
      let w = get_non_informative_witness f g_then (comp_u c_then) (comp_res c_then) in
      let e_then_typing =
        T_Lift _ _ _ _ e_then_typing (Lift_STGhost_STAtomic _ _ w) in
      let (| c, e1_typing, e2_typing |) =
        combine_if_branches _ _ _ _ e_then_typing _ _ _ e_else_typing in
      (| c, e1_typing, e2_typing |)
    | _, C_STGhost _ _ ->
      let w = get_non_informative_witness f g_else (comp_u c_else) (comp_res c_else) in
      let e_else_typing =
        T_Lift _ _ _ _ e_else_typing (Lift_STGhost_STAtomic _ _ w) in
      combine_if_branches _ _ _ _ e_then_typing _ _ _ e_else_typing
    | _, _ -> T.fail "Cannot combine then and else branches (incompatible effects)"
  end
  else T.fail "Cannot combine then and else branches (different st_comp)"
#pop-options

#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 10"
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
  let t =
    if has_pure_vprops pre &&
       (match t with
        | Tm_STApp (Tm_FVar l) _ _ -> l <> elim_pure_lid
        | _ -> true)
    then snd (maybe_add_elim_pure pre t)
    else t in
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
          T.fail
            (Printf.sprintf
               "Unexpected head type in stateful application (head: %s, comp_typ: %s, and arg: %s"
               (P.term_to_string head)
               (P.comp_to_string comp_typ)
               (P.term_to_string arg))
      )
      else T.fail "Unexpected qualifier"
    )
    
    | _ -> T.fail (Printf.sprintf "Unexpected head type in impure application: %s" (P.term_to_string ty_head))
    end

  | Tm_Bind _ _ ->
    check_bind f g t pre pre_typing post_hint (check' true)
    
  | Tm_If b e1 e2 post_if ->
    let (| b, b_typing |) =
      check_tot_with_expected_typ f g b tm_bool in

    let post =
      match post_if, post_hint with
      | None, Some _ -> post_hint
      | Some _, None -> post_if
      | _, _ -> T.fail "Either two annotations for if post or none" in

    let hyp = fresh g in
    let g_then =
      (hyp, Inl (mk_eq2 U_zero tm_bool b tm_true))::g in
    let (| e1, c1, e1_typing |) =
      //
      // TODO: this is unnecessary
      //       we have typing of pre in g
      //       weakening should give typing of pre in g_then
      //
      let pre_typing : tot_typing f g_then pre Tm_VProp =
        check_vprop_no_inst f g_then pre in
      let (| e1, c1, e1_typing |) =
        check' allow_inst f g_then e1 pre pre_typing post in
      let (| c1, e1_typing |) =
        force_st pre_typing (| c1, e1_typing |) in
      (| e1, c1, e1_typing |) in

    let g_else =
      (hyp, Inl (mk_eq2 U_zero tm_bool b tm_false))::g in
    let (| e2, c2, e2_typing |) =
      //
      // TODO: this is unnecessary
      //       we have typing of pre in g
      //       weakening should give typing of pre in g_then
      //
      let pre_typing : tot_typing f g_else pre Tm_VProp =
        check_vprop_no_inst f g_else pre in
      let (| e2, c2, e2_typing |) =
        check' allow_inst f g_else e2 pre pre_typing post in
      let (| c2, e2_typing |) =
        force_st pre_typing (| c2, e2_typing |) in
      (| e2, c2, e2_typing |) in
    let (| c, e1_typing, e2_typing |) =
      combine_if_branches _ _ _ _ e1_typing _ _ _ e2_typing in
    (| Tm_If b e1 e2 post_if,
       c,
       T_If g b e1 e2 post_if c hyp (E b_typing) e1_typing e2_typing |)

  | Tm_UVar _ ->
    T.fail "Unexpected Tm_Uvar in check"
#pop-options

let check = check' true
