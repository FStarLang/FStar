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
module FV = Pulse.Typing.FV

#push-options "--z3rlimit_factor 2"
let replace_equiv_post
  (f:RT.fstar_top_env)
  (g:env)
  (c:pure_comp{stateful_comp c /\ freevars_comp c `Set.subset` FV.vars_of_env g})
  (post_hint:option term)

  : T.Tac (c1:pure_comp { stateful_comp c1 /\ comp_pre c1 == comp_pre c } & st_equiv f g c c1) =

  let {u=u_c;res=res_c;pre=pre_c;post=post_c} = st_comp_of_comp c in
  let x = fresh g in //We could pick x here fresh with respect to both g and post_hint, rather than failing
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
    if (x `Set.mem` freevars post)
    then T.fail "Unexpected variable clash with annotated postcondition"
    else (
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
    )
#pop-options

#push-options "--query_stats"
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
    let pre_opened = 
      match pre_hint with
      | None -> T.fail "Cannot typecheck an function without a precondition"
      | Some pre_hint -> open_term pre_hint x in
    match check_tot true f g' pre_opened with
    | (| pre_opened, Tm_VProp, pre_typing |) ->
      let pre = close_term pre_opened x in
      let post =
        match post_hint with
        | None -> None
        | Some post ->
          let post = open_term' post (Tm_Var {nm_ppname=RT.pp_name_default;nm_index=x}) 1 in
          Some post
      in
      let (| body', c_body, body_typing |) = check f g' (open_term body x) pre_opened (E pre_typing) post in
      FV.src_typing_freevars body_typing;
      let body_closed = close_term body' x in
      assume (open_term body_closed x == body');

      let tt = T_Abs g ppname x qual t u body_closed c_body t_typing body_typing in
      let tres = Tm_Arrow {binder_ty=t;binder_ppname=ppname} qual (close_comp c_body x) in
      (| Tm_Abs {binder_ty=t;binder_ppname=ppname} qual None body_closed None, 
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

#push-options "--z3rlimit_factor 20"
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

  if eq_st_comp (st_comp_of_comp c_then) (st_comp_of_comp c_else)
  then begin
    match c_then, c_else with
    | C_ST _, C_ST _ -> (| c_then, e_then_typing, e_else_typing |)
    | C_STAtomic inames1 _, C_STAtomic inames2 _
    | C_STGhost inames1 _, C_STGhost inames2 _ ->
      if eq_tm inames1 inames2
      then (| c_then, e_then_typing, e_else_typing |)
      else T.fail "Cannot combine then and else branches (different inames)"
    | C_ST _, C_STAtomic inames _ ->
      if eq_tm inames Tm_EmpInames
      then begin
        let e_else_typing =
          T_Lift g_else e_else c_else c_then e_else_typing
            (Lift_STAtomic_ST g_else c_else) in
        (| c_then, e_then_typing, e_else_typing |)
      end
      else T.fail "Cannot lift STAtomic else branch to match then"
    | C_STAtomic inames _, C_ST _ ->
      if eq_tm inames Tm_EmpInames
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
let check_comp (f:RT.fstar_top_env)
               (g:env) 
               (c:pure_comp_st)
               (pre_typing:tot_typing f g (comp_pre c) Tm_VProp)
  : T.Tac (comp_typing f g c (comp_u c))
  = let check_st_comp (st:st_comp { is_pure_st_comp st /\
                                    comp_u c == st.u /\
                                    comp_pre c == st.pre /\
                                    comp_res c == st.res /\
                                    comp_post c == st.post } )
      : T.Tac (st_comp_typing f g st)
      = let (| u, t_u |) = check_universe f g st.res in 
        if u <> comp_u c
        then T.fail "Unexpected universe"
        else (
          let x = fresh g in
          assume (~(x `Set.mem` freevars (comp_post c)));
          let gx = (x, Inl st.res)::g in
          let (| ty, post_typing |) = check_tot_no_inst f gx (open_term (comp_post c) x) in
          if not (eq_tm ty Tm_VProp)
          then T.fail "Ill-typed postcondition"
          else (
            assert (ty == Tm_VProp);
            STC g st x t_u pre_typing (E post_typing)
          )
        )
    in
    match c with
    | C_ST st -> 
      let stc = check_st_comp st in
      CT_ST _ _ stc
    | C_STAtomic i st -> 
      let stc = check_st_comp st in
      let (| ty, i_typing |) = check_tot_no_inst f g i in
      if not (eq_tm ty Tm_Inames)
      then T.fail "Ill-typed inames"
      else CT_STAtomic _ _ _ (E i_typing) stc
    | C_STGhost i st -> 
      let stc = check_st_comp st in
      let (| ty, i_typing |) = check_tot_no_inst f g i in
      if not (eq_tm ty Tm_Inames)
      then T.fail "Ill-typed inames"
      else CT_STGhost _ _ _ (E i_typing) stc

               
let check_if (f:RT.fstar_top_env)
             (g:env)
             (b:term)
             (e1 e2:term)
             (pre:pure_term)
             (pre_typing: tot_typing f g pre Tm_VProp)
             (post:term) 
             (check:check_t)
  : T.Tac (t:term &
           c:pure_comp { stateful_comp c ==> comp_pre c == pre } &
           src_typing f g t c)
  = let (| b, b_typing |) =
      check_tot_with_expected_typ f g b tm_bool in
    let hyp = fresh g in
    let g_with_eq (eq_v:pure_term) =
      (hyp, Inl (mk_eq2 U_zero tm_bool b eq_v))::g
    in
    let check_branch (eq_v:pure_term) (br:term)
      : T.Tac (br:term { ~(hyp `Set.mem` freevars br) } &
               c:pure_comp { stateful_comp c /\ comp_pre c == pre } &
               src_typing f (g_with_eq eq_v) br c)
      = let g_with_eq = g_with_eq eq_v in
        //
        // TODO: pre_typing is unnecessary
        //       we have typing of pre in g
        //       weakening should give typing of pre in g_then
        //
        let pre_typing = check_vprop_no_inst f g_with_eq pre in
        let (| br, c, br_typing |) =
            check f g_with_eq br pre pre_typing (Some post)
        in
        if hyp `Set.mem` freevars br
        then T.fail "Illegal use of control-flow hypothesis in branch"
        else (
          let (| c, br_typing |) = force_st pre_typing (| c, br_typing |) in
          (| br, c, br_typing |)
        )
    in
    let (| e1, c1, e1_typing |) = check_branch tm_true e1 in
    let (| e2, c2, e2_typing |) = check_branch tm_false e2 in    
    let (| c, e1_typing, e2_typing |) =
      combine_if_branches _ _ _ _ e1_typing _ _ _ e2_typing in
    let c_typing = check_comp _ _ c pre_typing in //Would be better to have post_typing already, rather than re-check here
    (| Tm_If b e1 e2 None,
       c,
       T_If g b e1 e2 c _ hyp (E b_typing) e1_typing e2_typing (E c_typing) |)

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
    then (
      FV.src_typing_freevars d_c;
      let (| c1, c_c1_eq |) = replace_equiv_post f g c post_hint in
      (| t, c1, T_Equiv _ _ _ _ d_c c_c1_eq |)
    )
    else (| t, c, d_c |)
  in
  //
  // Should revisit this heuristic to add elim_pure
  //   whenever there is a pure vprop in the context
  // This doesn't work well when we have intro_pure in the program
  //
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
  | Tm_ExistsSL _ _ _
  | Tm_ForallSL _ _ _
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
    let post =
      match post_if, post_hint with
      | None, Some p -> p
      | Some p, None -> p
      | _, _ -> T.fail "Either two annotations for if post or none"
    in
    check_if f g b e1 e2 pre pre_typing post (check' true)

  | Tm_ElimExists t ->
    let (| t, t_typing |) = check_vprop f g t in
    (match t with
     | Tm_ExistsSL u ty p ->
       // Could this come from inversion of t_typing?
       let (| u', ty_typing |) = check_universe f g ty in
       if u = u'
       then let x = fresh g in
            let d = T_ElimExists g u ty p x ty_typing t_typing in
            repack (try_frame_pre pre_typing d) true
       else T.fail "Universe checking failed in elim_exists"
     | _ -> T.fail "elim_exists argument not a Tm_ExistsSL")

  | Tm_IntroExists t e ->
    let (| t, t_typing |) = check_vprop f g t in
    (match t with
     | Tm_ExistsSL u ty p ->
       // Could this come from inversion of t_typing?
       let (| u', ty_typing |) = check_universe f g ty in
       if u = u'
       then let (| e, e_typing |) = check_tot_with_expected_typ f g e ty in
            let d = T_IntroExists g u ty p e ty_typing t_typing (E e_typing) in
            repack (try_frame_pre pre_typing d) true
       else T.fail "Universe checking failed in intro_exists"
     | _ -> T.fail "elim_exists argument not a Tm_ExistsSL")

  | Tm_While inv cond body ->
    let (| inv, inv_typing |) =
      check_vprop f g (Tm_ExistsSL U_zero tm_bool inv) in
    (match inv with
     | Tm_ExistsSL U_zero (Tm_FVar ["Prims"; "bool"]) inv ->
       // Should get from inv_typing
       let cond_pre_typing =
         check_vprop_no_inst f g (comp_pre (comp_while_cond inv)) in
       let (| cond, cond_comp, cond_typing |) =
         check' allow_inst f g cond (comp_pre (comp_while_cond inv))
           cond_pre_typing (Some (comp_post (comp_while_cond inv))) in
       if eq_comp cond_comp (comp_while_cond inv)
       then begin
         let body_pre_typing =
           check_vprop_no_inst f g (comp_pre (comp_while_body inv)) in
         let (| body, body_comp, body_typing |) =
           check' allow_inst f g body (comp_pre (comp_while_body inv))
             body_pre_typing (Some (comp_post (comp_while_body inv))) in
         if eq_comp body_comp (comp_while_body inv)
         then let d = T_While g inv cond body inv_typing cond_typing   body_typing in
              repack (try_frame_pre pre_typing d) true
         else T.fail "Cannot typecheck while loop body"
       end
       else T.fail "Cannot typecheck while loop condition"
     | _ -> T.fail "Typechecked invariant is not an exists")

  | Tm_UVar _ ->
    T.fail "Unexpected Tm_Uvar in check"
#pop-options

let check = check' true
