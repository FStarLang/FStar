module Pulse.Checker
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Framing
open Pulse.Checker.Bind
module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.Builtins
module FV = Pulse.Typing.FV
module RU = Pulse.RuntimeUtils
module Metatheory = Pulse.Typing.Metatheory

let terms_to_string (t:list term)
  : T.Tac string 
  = String.concat "\n" (T.map Pulse.Syntax.Printer.term_to_string t)

exception Framing_failure of framing_failure

let try_frame_pre (#g:env)
                  (#t:st_term)
                  (#pre:term)
                  (pre_typing: tot_typing g pre Tm_VProp)
                  (#c:comp_st)
                  (t_typing: st_typing g t c)
  : T.Tac (c':comp_st { comp_pre c' == pre } &
           st_typing g t c')
  = let g = push_context "try_frame_pre" g in
    match Pulse.Checker.Framing.try_frame_pre #g pre_typing t_typing with
    | Inl ok -> ok
    | Inr fail -> T.raise (Framing_failure fail)

#push-options "--z3rlimit_factor 2"
let replace_equiv_post
      (g:env)
      (c:comp{stateful_comp c /\ freevars_comp c `Set.subset` FV.vars_of_env g})
      (ct:Metatheory.comp_typing_u g c)
      (post_hint:post_hint_opt g)
  : T.Tac (c1:comp { stateful_comp c1 /\ comp_pre c1 == comp_pre c } & st_equiv g c c1)
  = let g = push_context "replace_equiv_post" g in
    let {u=u_c;res=res_c;pre=pre_c;post=post_c} = st_comp_of_comp c in
    let st_typing = Metatheory.comp_typing_inversion ct in
    let (| res_c_typing, pre_c_typing, x, post_c_typing |) = Metatheory.st_comp_typing_inversion st_typing in
    let px = v_as_nv x in
    let g_post = extend x (Inl res_c) g in
    let post_c_opened = open_term_nv post_c px in
    match post_hint with
    | None ->
      (| c,
         ST_VPropEquiv
           g c c x pre_c_typing res_c_typing post_c_typing
           (VE_Refl _ _)
           (VE_Refl _ _) |)
    | Some post ->
      if (x `Set.mem` freevars post.post)
      then T.fail "Unexpected variable clash with annotated postcondition"
      else (
        let post_opened = open_term_nv post.post px in
        let post_c_post_eq
          : vprop_equiv g_post post_c_opened post_opened
          = check_vprop_equiv (push_context "check_vprop_equiv" g_post)
                              post_c_opened
                              post_opened
                              post_c_typing
        in
        let st_comp_with_post : st_comp = {
          u=u_c;
          res=res_c;
          pre=pre_c;
          post=close_term post_opened x
        } in
        let c_with_post = c `with_st_comp` st_comp_with_post in
        assume (open_term (close_term post_opened x) x == post_opened);
        (| c_with_post,
           ST_VPropEquiv
             g c c_with_post x pre_c_typing res_c_typing post_c_typing
             (VE_Refl _ _)
             post_c_post_eq |)
      )
#pop-options

#push-options "--query_stats"
let check_abs
  (g:env)
  (t:st_term{Tm_Abs? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (t:st_term &
           c:comp { stateful_comp c ==> comp_pre c == pre } &
           st_typing g t c) =
  match t.term with  
  | Tm_Abs { b = {binder_ty=t;binder_ppname=ppname}; q=qual; pre=pre_hint; body; ret_ty; post=post_hint } ->
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
      let post =
        match post_hint with
        | None -> None
        | Some post ->
          let post = open_term' post (tm_var {nm_ppname=RT.pp_name_default;nm_index=x;nm_range=Range.range_0}) 1 in
          let post_hint_typing : post_hint_t = Pulse.Checker.Common.intro_post_hint g' ret_ty post in
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

let has_pure_vprops (pre:term) = L.existsb Tm_Pure? (vprop_as_list pre)
let elim_pure_explicit_lid = mk_steel_wrapper_lid "elim_pure_explicit"

let default_binder_annot = {
    binder_ppname = RT.pp_name_default;
    binder_ty = Tm_Unknown
}
   
let maybe_add_elim_pure (pre:list term) (t:st_term) : T.Tac (bool & st_term) =
  let pure_props =
    L.flatten (L.map (fun (t:term) ->
                      match t with
                      | Tm_Pure p -> [p]
                      | _ -> []) pre) in

  if L.length pure_props = 0
  then false, t
  else (
    true,
    L.fold_left 
      (fun t (p:term) ->
        let elim_pure_tm =
          Tm_STApp { head = tm_fvar (as_fv elim_pure_explicit_lid);
                     arg_qual = None;
                     arg = p }
        in
        let bind =
          Tm_Bind { binder = default_binder_annot;
                    head = wr (Tm_Protect { t = wr elim_pure_tm });
                    body = t }
        in
        wr bind)
      t
      pure_props
  )

#push-options "--z3rlimit_factor 40"
let rec combine_if_branches
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  : T.TacH (c:comp_st{comp_pre c == comp_pre c_then} &
            st_typing g_then e_then c &
            st_typing g_else e_else c)
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
      let w = get_non_informative_witness g_then (comp_u c_then) (comp_res c_then) in
      let e_then_typing =
        T_Lift _ _ _ _ e_then_typing (Lift_STGhost_STAtomic _ _ w) in
      let (| c, e1_typing, e2_typing |) =
        combine_if_branches _ _ _ e_then_typing _ _ _ e_else_typing in
      (| c, e1_typing, e2_typing |)
    | _, C_STGhost _ _ ->
      let w = get_non_informative_witness g_else (comp_u c_else) (comp_res c_else) in
      let e_else_typing =
        T_Lift _ _ _ _ e_else_typing (Lift_STGhost_STAtomic _ _ w) in
      combine_if_branches _ _ _ e_then_typing _ _ _ e_else_typing
    | _, _ -> T.fail "Cannot combine then and else branches (incompatible effects)"
  end
  else T.fail "Cannot combine then and else branches (different st_comp)"
#pop-options

#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 10"
let check_comp (g:env) 
               (c:comp_st)
               (pre_typing:tot_typing g (comp_pre c) Tm_VProp)
  : T.Tac (comp_typing g c (comp_u c))
  = let check_st_comp (st:st_comp { comp_u c == st.u /\
                                    comp_pre c == st.pre /\
                                    comp_res c == st.res /\
                                    comp_post c == st.post } )
      : T.Tac (st_comp_typing g st)
      = let (| u, t_u |) = check_universe g st.res in 
        if not (eq_univ u (comp_u c))
        then T.fail "Unexpected universe"
        else (
          let x = fresh g in
          let px = v_as_nv x in
          assume (~(x `Set.mem` freevars (comp_post c)));
          let gx = extend x (Inl st.res) g in
          let (| ty, post_typing |) = core_check_term gx (open_term_nv (comp_post c) px) in
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
      let (| ty, i_typing |) = core_check_term g i in
      if not (eq_tm ty Tm_Inames)
      then T.fail "Ill-typed inames"
      else CT_STAtomic _ _ _ (E i_typing) stc
    | C_STGhost i st -> 
      let stc = check_st_comp st in
      let (| ty, i_typing |) = core_check_term g i in
      if not (eq_tm ty Tm_Inames)
      then T.fail "Ill-typed inames"
      else CT_STGhost _ _ _ (E i_typing) stc

let intro_comp_typing (g:env) 
                      (c:comp_st)
                      (pre_typing:tot_typing g (comp_pre c) Tm_VProp)
                      (res_typing:universe_of g (comp_res c) (comp_u c))
                      (x:var { Metatheory.fresh_wrt x g (freevars (comp_post c)) })
                      (post_typing:tot_typing (extend x (Inl (comp_res c)) g) (open_term (comp_post c) x) Tm_VProp)
  : T.Tac (comp_typing g c (comp_u c))
  = let intro_st_comp_typing (st:st_comp { comp_u c == st.u /\
                                           comp_pre c == st.pre /\
                                           comp_res c == st.res /\
                                           comp_post c == st.post } )
      : T.Tac (st_comp_typing g st)
      = STC g st x res_typing pre_typing post_typing
    in
    match c with
    | C_ST st -> 
      let stc = intro_st_comp_typing st in
      CT_ST _ _ stc
    | C_STAtomic i st -> 
      let stc = intro_st_comp_typing st in
      let (| ty, i_typing |) = core_check_term g i in
      if not (eq_tm ty Tm_Inames)
      then T.fail "Ill-typed inames"
      else CT_STAtomic _ _ _ (E i_typing) stc
    | C_STGhost i st -> 
      let stc = intro_st_comp_typing st in
      let (| ty, i_typing |) = core_check_term g i in
      if not (eq_tm ty Tm_Inames)
      then T.fail "Ill-typed inames"
      else CT_STGhost _ _ _ (E i_typing) stc

let check_if (g:env)
             (b:term)
             (e1 e2:st_term)
             (pre:term)
             (pre_typing: tot_typing g pre Tm_VProp)
             (post_hint:post_hint_for_env g)
             (check:check_t)
  : T.Tac (t:st_term &
           c:comp { stateful_comp c ==> comp_pre c == pre } &
           st_typing g t c)
  = let (| b, b_typing |) =
      check_term_with_expected_type g b tm_bool in
    let post = post_hint.post in
    let hyp = fresh g in
    let g_with_eq (eq_v:term) =
        extend hyp (Inl (mk_eq2 u0 tm_bool b eq_v)) g
    in
    let check_branch (eq_v:term) (br:st_term)
      : T.Tac (br:st_term { ~(hyp `Set.mem` freevars_st br) } &
               c:comp { stateful_comp c /\ comp_pre c == pre } &
               st_typing (g_with_eq eq_v) br c)
      = let g_with_eq = g_with_eq eq_v in
        //
        // TODO: pre_typing is unnecessary
        //       we have typing of pre in g
        //       weakening should give typing of pre in g_then
        //
        let pre_typing = check_vprop_with_core g_with_eq pre in
        let (| br, c, br_typing |) =
            check g_with_eq br pre pre_typing (Some post_hint)
        in
        if hyp `Set.mem` freevars_st br
        then T.fail "Illegal use of control-flow hypothesis in branch"
        else if C_Tot? c
        then T.fail "Branch computation type not st"
        else (| br, c, br_typing |)
        //   let (| c, br_typing |) = force_st pre_typing (| c, br_typing |) in
        //   (| br, c, br_typing |)
        // )
    in
    let (| e1, c1, e1_typing |) = check_branch tm_true e1 in
    let (| e2, c2, e2_typing |) = check_branch tm_false e2 in    
    let (| c, e1_typing, e2_typing |) =
      combine_if_branches _ _ _ e1_typing _ _ _ e2_typing in
    let c_typing = 
      let x = fresh g in
      if x `Set.mem` freevars post //exclude this
      then T.fail "Unexpected name clash"
      else if not (eq_tm (comp_res c) post_hint.ret_ty &&
                   eq_univ (comp_u c) post_hint.u &&
                   eq_tm (comp_post c) post_hint.post) //exclude by check' strengthening
      then (
        T.fail "Unexpected result type in branches"
      )
      else (
        let post_typing = Checker.Common.post_hint_typing g post_hint x in
        intro_comp_typing g c pre_typing post_typing.ty_typing x post_typing.post_typing
      )
    in
    (| _, //Tm_If b e1 e2 None,
       c,
       T_If g b e1 e2 c _ hyp (E b_typing) e1_typing e2_typing (E c_typing) |)

let repack (#g:env) (#pre:term) (#t:st_term)
           (x:(c:comp_st { comp_pre c == pre } & st_typing g t c))
           (post_hint:post_hint_opt g)
           (apply_post_hint:bool)
  : T.Tac (t:st_term &
           c:comp {stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c)
  = let (| c, d_c |) = x in
    if apply_post_hint && stateful_comp c
    then (
      FV.st_typing_freevars d_c;
      let (| c1, c_c1_eq |) = replace_equiv_post g c (Metatheory.st_typing_correctness d_c) post_hint in
      (| t, c1, T_Equiv _ _ _ _ d_c c_c1_eq |)
    )
    else (| t, c, d_c |)

let vprop_as_list_typing (#g:env) (#p:term) (t:tot_typing g p Tm_VProp) (x:term { List.Tot.memP x (vprop_as_list p) })
  : tot_typing g x Tm_VProp
  = assume false; t
  
let check_elim_exists
  (g:env)
  (t:st_term{Tm_ElimExists? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c) =
  let Tm_ElimExists { p = t } = t.term in
  let t_t_typing : (t:term & tot_typing g t Tm_VProp ) = 
      match t with
      | Tm_Unknown -> (
        //There should be exactly one exists_ vprop in the context and we eliminate it      
        let ts = vprop_as_list pre in
        let exist_tms = List.Tot.Base.filter (function | Tm_ExistsSL _ _ _ _ -> true | _ -> false) ts in
        match exist_tms with
        | [one] -> 
          assume (one `List.Tot.memP` ts);
          (| one, vprop_as_list_typing pre_typing one |) //shouldn't need to check this again
        | _ -> 
          T.fail 
            (Printf.sprintf "Could not decide which exists term to eliminate: choices are\n%s"
               (terms_to_string exist_tms))
        )
      | _ ->
        let t, _ = instantiate_term_implicits g t in
        assume false;
        (| t, pre_typing |)
//        check_vprop g t
  in
  let (| t, t_typing |) = t_t_typing in
//  let (| t, t_typing |) = check_vprop g t in
  match t with
  | Tm_ExistsSL u ty p _ ->
    // T.print (Printf.sprintf "LOG ELIM EXISTS: %s\n"
    //                         (P.term_to_string t));

    // Could this come from inversion of t_typing?
    let (| u', ty_typing |) = check_universe g ty in
    if eq_univ u u'
    then let x = fresh g in
         let d = T_ElimExists g u ty p x ty_typing t_typing in
         repack (try_frame_pre pre_typing d) post_hint true
    else T.fail "Universe checking failed in elim_exists"
  | _ -> T.fail "elim_exists argument not a Tm_ExistsSL"

let is_intro_exists_erased (st:st_term) = 
  match st.term with
  | Tm_IntroExists { erased } -> erased
  | _ -> false

let intro_exists_vprop (st:st_term { Tm_IntroExists? st.term })  = 
  match st.term with
  | Tm_IntroExists { p } -> p

let intro_exists_witness_singleton (st:st_term)  = 
  match st.term with
  | Tm_IntroExists { witnesses = [_] } -> true
  | _ -> false

let check_intro_exists_erased
  (g:env)
  (st:st_term{intro_exists_witness_singleton st /\
              is_intro_exists_erased st})
  (vprop_typing: option (tot_typing g (intro_exists_vprop st) Tm_VProp))
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c) =

  let Tm_IntroExists { p=t; witnesses=[e] } = st.term in
  let (| t, t_typing |) = 
    match vprop_typing with
    | Some typing -> (| t, typing |)
    | _ -> check_vprop g t
  in
  match t with
  | Tm_ExistsSL u ty p _ ->
    Pulse.Typing.FV.tot_typing_freevars t_typing;
    let ty_typing, _ = Metatheory.tm_exists_inversion #g #u #ty #p t_typing (fresh g) in
    let (| e, e_typing |) = 
        check_term_with_expected_type g e (mk_erased u ty) in
    let d = T_IntroExistsErased g u ty p e ty_typing t_typing (E e_typing) in
    repack (try_frame_pre pre_typing d) post_hint true
  | _ -> T.fail "elim_exists argument not a Tm_ExistsSL"


let check_intro_exists
  (g:env)
  (st:st_term{intro_exists_witness_singleton st /\ not (is_intro_exists_erased st)})
  (vprop_typing: option (tot_typing g (intro_exists_vprop st) Tm_VProp))
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c) =

  let Tm_IntroExists { p=t; witnesses=[e] } = st.term in
  let (| t, t_typing |) =
    match vprop_typing with
    | Some typing -> (| t, typing |)
    | _ -> check_vprop g t    
  in
  match t with
  | Tm_ExistsSL u ty p _ ->
    Pulse.Typing.FV.tot_typing_freevars t_typing;
    let ty_typing, _ = Metatheory.tm_exists_inversion #g #u #ty #p t_typing (fresh g) in
    let (| e, e_typing |) = 
        check_term_with_expected_type g e ty in
    let d = T_IntroExists g u ty p e ty_typing t_typing (E e_typing) in
    repack (try_frame_pre pre_typing d) post_hint true
  | _ -> T.fail "elim_exists argument not a Tm_ExistsSL"

let check_intro_exists_either
  (g:env)
  (st:st_term{intro_exists_witness_singleton st})
  (vprop_typing: option (tot_typing g (intro_exists_vprop st) Tm_VProp))
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c)
  = 
  // T.print (Printf.sprintf "LOG INTRO EXISTS: %s"
  //                           (P.term_to_string (intro_exists_vprop st)));
    if is_intro_exists_erased st
    then check_intro_exists_erased g st vprop_typing pre pre_typing post_hint
    else check_intro_exists g st vprop_typing pre pre_typing post_hint

let rec prepare_instantiations (out:list (vprop & either term term)) goal_vprop witnesses
  : T.Tac (vprop & list (vprop & either term term))
  = match witnesses, goal_vprop with
    | [], Tm_ExistsSL u ty p _ ->  
      let next_goal_vprop, inst =
          let t : term = snd (Pulse.Checker.Inference.gen_uvar ()) in
          open_term' p t 0, Inr t
      in
      prepare_instantiations ((goal_vprop, inst)::out) next_goal_vprop []

    | [], _ -> 
      goal_vprop, out
      
    | t :: witnesses, Tm_ExistsSL u ty p _ ->
      let next_goal_vprop, inst =
          match t with
          | Tm_Unknown ->
            let t : term = snd (Pulse.Checker.Inference.gen_uvar ()) in
            open_term' p t 0, Inr t
          | _ ->
            open_term' p t 0, Inl t
      in
      prepare_instantiations ((goal_vprop, inst)::out) next_goal_vprop witnesses
    |  _ ->
       T.fail "Unexpected number of instantiations in intro"


let maybe_infer_intro_exists
  (g:env)
  (st:st_term{Tm_IntroExists? st.term})
  (pre:term)
  : T.Tac st_term
  = let remove_pure_conjuncts t =
        let rest, pure = 
            List.Tot.partition
              (function Tm_Pure _ | Tm_Emp -> false | _ -> true)
              (vprop_as_list t)
        in
        let rest =
          match list_as_vprop rest with
          | Tm_Star t Tm_Emp -> t
          | Tm_Star Tm_Emp t -> t        
          | t -> t
        in
        rest, pure
    in
    (* Weird: defining this here causes extraction to crash with
       Failure("This should not happen (should have been handled at Tm_abs level)")
     *)                                                                           
    // let rec prepare_instantiations (out:list (vprop & term)) goal_vprop witnesses
    //   : T.Tac (vprop & list (vprop & term))
    //   = match witnesses, goal_vprop with
    //     | [], _ -> 
    //       goal_vprop, out
    //     | t :: witnesses, Tm_ExistsSL u ty p _ ->
    //       let inst =
    //         match t with
    //         | Tm_Unknown -> gen_uvar ty
    //         | _ -> t
    //       in
    //       let next_goal_vprop = open_term' p inst 0 in
    //       prepare_instantiations ((goal_vprop, inst)::out) next_goal_vprop witnesses
    //     |  _ ->
    //       T.fail "Unexpected number of instantiations in intro"
    // in
    let Tm_IntroExists {erased; p=t; witnesses} = st.term in
    let (| t, t_typing |) = check_vprop g t in
    let goal_vprop, insts = prepare_instantiations [] t witnesses in
    let goal_vprop, pure_conjuncts = remove_pure_conjuncts goal_vprop in      
    let solutions = Pulse.Checker.Inference.try_inst_uvs_in_goal pre goal_vprop in
    let maybe_solve_pure solutions p =
      let p = Pulse.Checker.Inference.apply_solution solutions p in
      match p with
      | Tm_Pure p -> (
          match is_eq2 p with
          | Some (l, r) ->
            let open Pulse.Checker.Inference in
            if contains_uvar l
            ||  contains_uvar r
            then let sols = try_unify l r in
                 sols@solutions
            else solutions
          | _ -> solutions
        )
      | _ -> solutions
    in
    let solutions = T.fold_left maybe_solve_pure solutions pure_conjuncts in
    let mk_hide (e:term) : term =
        let hd = tm_fvar (as_fv hide_lid) in
        tm_pureapp hd None e
    in    
    let solutions = 
      List.Tot.map
        (fun (u, v) -> 
          let sol = Pulse.Checker.Inference.apply_solution solutions v in
          match unreveal sol with
          | Some _ -> u, sol
          | _ -> u, mk_hide sol)
        solutions
    in
    let wr t = { term = t; range = st.range } in
    let rec build_instantiations solutions insts
      : T.Tac st_term 
      = let one_inst (v, i) =
          let v = Pulse.Checker.Inference.apply_solution solutions v in
          match i with
          | Inl user_provided ->
            wr (Tm_IntroExists {erased=false; p=v; witnesses=[user_provided]})

          | Inr inferred ->
            let sol = Pulse.Checker.Inference.apply_solution solutions inferred in
            match unreveal sol with
            | Some sol ->
              wr (Tm_IntroExists {erased=true; p=v; witnesses=[sol]})
            | _ ->
              wr (Tm_IntroExists {erased=true; p=v; witnesses=[sol]})
        in
        match insts with
        | [] -> T.fail "Impossible"
        | [hd] -> wr (Tm_Protect { t = one_inst hd })
        | hd::tl -> wr (Tm_Protect 
                          { t = wr (Tm_Bind { binder = default_binder_annot;
                                              head = wr (Tm_Protect { t = one_inst hd });
                                              body = build_instantiations solutions tl }) })
    in
    build_instantiations solutions insts

////////////////////////////////////////////////////
// While loops
///////////////////////////////////////////////////

let while_cond_comp_typing (#g:env) (u:universe) (ty:term) (inv_body:term)
                           (inv_typing:tot_typing g (Tm_ExistsSL u ty inv_body should_elim_false) Tm_VProp)
  : Metatheory.comp_typing_u g (comp_while_cond inv_body)
  = admit()

let while_body_comp_typing (#g:env) (u:universe) (ty:term) (inv_body:term)
                           (inv_typing:tot_typing g (Tm_ExistsSL u ty inv_body should_elim_false) Tm_VProp)
  : Metatheory.comp_typing_u g (comp_while_body inv_body)
  = admit()

#push-options "--ifuel 2"
let check_while
  (allow_inst:bool)
  (g:env)
  (t:st_term{Tm_While? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  (check':bool -> check_t)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c) =
  let g = push_context "while loop" g in
  let Tm_While { invariant=inv; condition=cond; body } = t.term in
  let (| ex_inv, inv_typing |) =
    check_vprop (push_context "invariant" g) (Tm_ExistsSL u0 tm_bool inv should_elim_true) in
  match ex_inv with
  | Tm_ExistsSL u ty inv _ ->
    if not (eq_tm ty tm_bool) ||
       not (eq_univ u u0)
    then T.fail "While loop invariant is exists but its witness type is not bool"
    else begin
      let while_cond_comp_typing = while_cond_comp_typing u ty inv inv_typing in
      let (| res_typing, cond_pre_typing, x, post_typing |) =
          Metatheory.(st_comp_typing_inversion (comp_typing_inversion while_cond_comp_typing))
      in
      let while_cond_hint
        : post_hint_for_env g
        = Checker.Common.post_hint_from_comp_typing while_cond_comp_typing
      in
      let (| cond, cond_comp, cond_typing |) =
        check' allow_inst
               (push_context "while condition" g)
               cond
               (comp_pre (comp_while_cond inv))
               cond_pre_typing
               (Some while_cond_hint)
      in
      if eq_comp cond_comp (comp_while_cond inv)
      then begin
        let while_body_comp_typing = while_body_comp_typing u ty inv inv_typing in
        let (| res_typing, body_pre_typing, x, post_typing |) = 
            Metatheory.(st_comp_typing_inversion (comp_typing_inversion while_body_comp_typing))
        in
        let while_post_hint
          : post_hint_for_env g
          = Checker.Common.post_hint_from_comp_typing while_body_comp_typing
        in
        let (| body, body_comp, body_typing |) =
            check' allow_inst
                   (push_context "while body" g)
                   body
                   (comp_pre (comp_while_body inv))
                   body_pre_typing
                   (Some while_post_hint)
        in
        if eq_comp body_comp (comp_while_body inv)
        then let d = T_While g inv cond body inv_typing cond_typing body_typing in
             repack (try_frame_pre pre_typing d) post_hint true
        else 
          T.fail
            (Printf.sprintf "Could not prove the inferred type of the while body matches the annotation\n\
                                   Inferred type = %s\n\
                                   Annotated type = %s\n"
                                   (P.comp_to_string body_comp)
                                   (P.comp_to_string (comp_while_body inv)))
    end
    else T.fail 
           (Printf.sprintf "Could not prove that the inferred type of the while condition matches the annotation\n\
                            Inferred type = %s\n\
                            Annotated type = %s\n"
                            (P.comp_to_string cond_comp)
                            (P.comp_to_string (comp_while_cond inv)))
    end
  | _ -> T.fail "Typechecked invariant is not an exists"

let range_of_head (t:st_term) : option (term & range) =
  match t.term with
  | Tm_STApp { head } ->
    let rec aux (t:term) : (term & range) =
      match t with
      | Tm_FStar _ r ->
        t, r
      | _ -> t, Range.range_0
    in
    Some (aux head)
  | _ -> None

let tag_of_term (t:term) =
  match t with
  | Tm_Emp -> "Tm_Emp"
  | Tm_Pure _ -> "Tm_Pure"
  | Tm_Star _ _ -> "Tm_Star"
  | Tm_ExistsSL _ _ _ _ -> "Tm_ExistsSL"
  | Tm_ForallSL _ _ _ -> "Tm_ForallSL"
  | Tm_VProp -> "Tm_VProp"
  | Tm_Inames -> "Tm_Inames"
  | Tm_EmpInames -> "Tm_EmpInames"
  | Tm_Unknown -> "Tm_Unknown"
  | Tm_FStar _ _ -> "Tm_FStar"

let tag_of_st_term (t:st_term) =
  match t.term with
  | Tm_Return _ -> "Tm_Return"
  | Tm_Abs _ -> "Tm_Abs"
  | Tm_STApp _ -> "Tm_STApp"
  | Tm_Bind _ -> "Tm_Bind"
  | Tm_TotBind _ -> "Tm_TotBind"
  | Tm_If _ -> "Tm_If"
  | Tm_ElimExists _ -> "Tm_ElimExists"
  | Tm_IntroExists _ -> "Tm_IntroExists"
  | Tm_While _ -> "Tm_While"
  | Tm_Par _ -> "Tm_Par"
  | Tm_WithLocal _ -> "Tm_WithLocal"
  | Tm_Rewrite _ -> "Tm_Rewrite"
  | Tm_Admit _ -> "Tm_Admit"
  | Tm_Protect _ -> "Tm_Protect"
  
let maybe_log t =
  let _ =
    match range_of_head t with
    | Some (head, range) ->
      T.print (Printf.sprintf "At location %s: Checking app with head (%s) = %s"
                         (T.range_to_string range)
                         (tag_of_term head)
                         (P.term_to_string head))
    | None -> ()
  in
  match t.term with
  | Tm_STApp { head; arg_qual=None; arg=p } ->
    begin match is_fvar head with
          | Some (l, _) ->
            if l = elim_pure_explicit_lid
            then T.print (Printf.sprintf "LOG ELIM PURE: %s\n"
                         (P.term_to_string p))
          | _ -> ()
    end
                    
  | Tm_STApp { head; arg_qual=None } ->
    begin match is_pure_app head with
          | Some (head, None, p) ->
            begin match is_fvar head with
                  | Some (l, _) ->
                    if l = mk_steel_wrapper_lid "intro_pure"
                    then T.print (Printf.sprintf "LOG INTRO PURE: %s\n"
                                 (P.term_to_string p))
                  | _ -> ()
            end
          | _ -> ()
    end
  | _ -> ()
    
let check_stapp
  (allow_inst:bool)
  (g:env)
  (t:st_term{Tm_STApp? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  (check':bool -> check_t)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c) =
  // maybe_log t;
  let range = t.range in
  let Tm_STApp { head; arg_qual=qual; arg } = t.term in

  //
  // c is the comp remaining after applying head to arg,
  //
  let infer_logical_implicits_and_check
    (t:term)
    (c:comp{C_Tot? c}) : T.Tac _ =

    match c with
    | C_Tot ty ->
      begin match is_arrow ty with
            | Some (_, Some Implicit, _) -> 
              //Some implicits to follow
              let t = Pulse.Checker.Inference.infer t ty pre range in
              check' false g t pre pre_typing post_hint
            | _ ->
              T.fail
                (Printf.sprintf
                   "Unexpected c in infer_logical_implicits_and_check (head: %s, comp_typ: %s, and arg: %s)"
                   (P.term_to_string head)
                   (P.comp_to_string c)
                   (P.term_to_string arg))
      end

    | _ ->
      T.fail
        (Printf.sprintf
           "Unexpected c in infer_logical_implicits_and_check (head: %s, comp_typ: %s, and arg: %s)"
           (P.term_to_string head)
           (P.comp_to_string c)
           (P.term_to_string arg)) in

  T.or_else
    (fun _ -> 
      let g = push_context "pure_app" g in    
      let pure_app = tm_pureapp head qual arg in
      let t, ty = instantiate_term_implicits g pure_app in
      infer_logical_implicits_and_check t (C_Tot ty))
    (fun _ ->
      let g = push_context "st_app" g in        
      let (| head, ty_head, dhead |) = check_term g head in
      match is_arrow ty_head with
      | Some ({binder_ty=formal;binder_ppname=ppname}, bqual, comp_typ) ->
        is_arrow_tm_arrow ty_head;
        assert (ty_head ==
                tm_arrow ({binder_ty=formal;binder_ppname=ppname}) bqual comp_typ);
        if qual = bqual
        then
         let (| arg, darg |) = check_term_with_expected_type g arg formal in
         match comp_typ with
         | C_ST res
         | C_STAtomic _ res
         | C_STGhost _ res ->
           // This is a real ST application
           let d = T_STApp g head formal qual comp_typ arg (E dhead) (E darg) in
          //  T.print (Printf.sprintf "ST application trying to frame, context: %s and pre: %s\n"
          //             (Pulse.Syntax.Printer.term_to_string pre)
          //             (Pulse.Syntax.Printer.term_to_string (comp_pre (open_comp_with comp_typ arg))));
           repack (try_frame_pre pre_typing d) post_hint true
         | _ ->
           let t = tm_pureapp head qual arg in
           let comp_typ = open_comp_with comp_typ arg in
           infer_logical_implicits_and_check t comp_typ
        else 
         T.fail (Printf.sprintf "(%s) Unexpected qualifier in head type %s of stateful application: head = %s, arg = %s"
                                (T.range_to_string t.range)
                                (P.term_to_string ty_head)
                                (P.term_to_string head)
                                (P.term_to_string arg))
    
     | _ -> T.fail (Printf.sprintf "Unexpected head type in impure application: %s" (P.term_to_string ty_head)))

let check_admit
  (g:env)
  (t:st_term{Tm_Admit? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c) =

  let Tm_Admit { ctag = c; typ=t; post } = t.term in
  let x = fresh g in
  let px = v_as_nv x in
  let res
    : (t:term & u:universe & universe_of g t u &
       post:vprop & tot_typing (extend x (Inl t) g) post Tm_VProp)
    = match post, post_hint with
      | None, None
      | Some _, Some _ ->
        T.fail "T_Admit: either no post or two posts"
      
      | Some post, _ ->
        let (| u, t_typing |) = check_universe g t in    
        let post_opened = open_term_nv post px in      
        let (| post, post_typing |) = 
            check_term_with_expected_type (extend x (Inl t) g) post_opened Tm_VProp
        in
        (| t, u, t_typing, post, E post_typing |)

      | _, Some post ->
        let post : post_hint_t = post in
        if x `Set.mem` freevars post.post
        then T.fail "Unexpected freevar clash in Tm_Admit"
        else (
          let post_typing_rec = Checker.Common.post_hint_typing g post x in
          let post_opened = open_term_nv post.post px in              
          (| post.ret_ty, post.u, post_typing_rec.ty_typing, post_opened, post_typing_rec.post_typing |)
        )
  in
  let (| t, u, t_typing, post_opened, post_typing |) = res in
  let post = close_term post_opened x in
  let s : st_comp = {u;res=t;pre;post} in
  assume (open_term (close_term post_opened x) x == post_opened);
  (|
     _, //Tm_Admit c u t None,
     comp_admit c s,
     T_Admit _ _ c (STC _ s x t_typing pre_typing post_typing)
  |)

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
         let ty_rec = Checker.Common.post_hint_typing g post x in
         (| open_term_nv post.post px, ty_rec.post_typing |)
  in
  assume (open_term (close_term post_opened x) x == post_opened);
  let post = close_term post_opened x in
  let d = T_Return g c use_eq u ty t post x uty (E d) post_typing in
  repack (try_frame_pre pre_typing d) post_hint true

let handle_framing_failure
    (g:env)
    (t0:st_term)
    (pre:term)
    (pre_typing: tot_typing g pre Tm_VProp)
    (post_hint:post_hint_opt g)
    (failure:framing_failure)
    (check:check_t)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c)
  = let wr t = { term = t; range = t0.range } in
    let add_intro_pure p t =
      let intro_pure_tm =
        wr (
          Tm_Protect
            { t = wr (Tm_STApp 
                        { head = tm_pureapp 
                                  (tm_fvar (as_fv (mk_steel_wrapper_lid "intro_pure")))
                                  None
                                  p;
                          arg_qual = None;
                          arg = tm_constant R.C_Unit }) }
        )
      in
      wr (
        Tm_Protect { t = wr (Tm_Bind { binder = default_binder_annot;
                                        head = intro_pure_tm;
                                        body = t }) }
      )
    in
    // T.print (Printf.sprintf
    //                  "Handling framing failure in term:\n%s\n\
    //                   with unmatched_pre={\n%s\n} and context={\n%s\n}"
    //                  (P.st_term_to_string t0)
    //                  (terms_to_string failure.unmatched_preconditions)
    //                  (terms_to_string failure.remaining_context));
    let pures, rest = 
      L.partition (function Tm_Pure _ -> true | _ -> false) failure.unmatched_preconditions
    in
    let t =
      T.fold_left 
        (fun t p ->
          match p with
          | Tm_Pure p -> add_intro_pure p t
          | _ -> T.fail "Impossible")
        (wr (Tm_Protect { t = t0 })) //don't elim what we just intro'd here
        pures
    in
    let rec handle_intro_exists rest (t:st_term)
      : T.Tac (t:st_term &
               c:comp{stateful_comp c ==> comp_pre c == pre} &
               st_typing g t c)
      = match rest with
        | [] -> check g t pre pre_typing post_hint
        | Tm_ExistsSL u ty p se :: rest ->
          let t = 
              Tm_Bind { 
                binder = default_binder_annot;
                head =
                   wr (Tm_Protect {
                          t = wr (Tm_IntroExists {
                                    erased=true;
                                    p=Tm_ExistsSL u ty p se;
                                    witnesses=[]
                                  });
                      });
                body = wr (Tm_Protect { t })
              }
          in
          handle_intro_exists rest (wr t)
        | _ ->
          T.fail (Printf.sprintf 
                      "Failed to satisfy the following preconditions:\n%s\nContext has\n%s\nat command %s\n"
                       (terms_to_string rest)
                       (terms_to_string failure.remaining_context)
                       (P.st_term_to_string t0))
    in
    handle_intro_exists rest t

let rec maybe_add_elims
           (g:env)
           (ctxt:list term)
           (t:st_term)
  : T.Tac st_term
  = let wr t' = { term = t'; range = t.range } in
    match ctxt with
    | [] -> t
    | Tm_ExistsSL u ty b se :: rest ->
      let e = wr (Tm_Protect { t = wr (Tm_ElimExists { p = Tm_ExistsSL u ty b se }) }) in
      let x = fresh g in
      let px = v_as_nv x in
      let g = extend x (Inl ty) g in
      let b = open_term_nv b px in
      let t = maybe_add_elims g [b] t in
      let t = close_st_term t x in
      let t = Tm_Bind { binder = default_binder_annot;
                        head = e;
                        body = wr (Tm_Protect { t }) } in
      maybe_add_elims g rest (wr t)
    | Tm_Pure p :: rest ->
      let elim_pure_tm = 
        wr (Tm_STApp { head = tm_fvar (as_fv elim_pure_explicit_lid);
                       arg_qual = None;
                       arg = p })
      in
      wr (
        Tm_Bind { binder = default_binder_annot;
                  head = wr (Tm_Protect { t = elim_pure_tm } );
                  body = wr (Tm_Protect { t = maybe_add_elims g rest t }) }
      )

    | Tm_Star p q :: rest ->
      maybe_add_elims g (p :: q :: rest) t    
      
    | _ :: rest ->
      maybe_add_elims g rest t

let rec unprotect t = 
  let wr t0 = { term = t0; range = t.range } in
  let protect t = { term = Tm_Protect { t }; range = t.range } in
  match t.term with
  | Tm_Protect { t = { term = Tm_Bind { binder; head; body } } } ->
    wr (Tm_Bind { binder; head=protect head; body })
  | Tm_Protect { t = { term = Tm_If { b; then_; else_; post }}} ->
    wr (Tm_If {b; then_=protect then_; else_=protect else_; post } )
  | Tm_Protect { t } ->
    unprotect t
  | _ -> t
  
let auto_elims (g:env) (ctxt:term) (t:st_term) =
  match t.term with
  | Tm_Protect _ -> unprotect t
  | _ ->
    let ctxt = vprop_as_list ctxt in
    let t = maybe_add_elims g ctxt t in 
    unprotect t
    
#push-options "--ifuel 2"
let rec print_st_head (t:st_term)
  : Tot string (decreases t) =
  match t.term with
  | Tm_Abs _  -> "Abs"
  | Tm_Protect p -> print_st_head p.t
  | Tm_Return p -> print_head p.term
  | Tm_Bind _ -> "Bind"
  | Tm_TotBind _ -> "TotBind"
  | Tm_If _ -> "If"
  | Tm_While _ -> "While"
  | Tm_Admit _ -> "Admit"
  | Tm_Par _ -> "Par"
  | Tm_Rewrite _ -> "Rewrite"
  | Tm_WithLocal _ -> "WithLocal"
  | Tm_STApp { head = p } -> print_head p
  | Tm_IntroExists _ -> "IntroExists"
  | Tm_ElimExists _ -> "ElimExists"  
and print_head (t:term) =
  match t with
  // | Tm_FVar fv
  // | Tm_UInst fv _ -> String.concat "." fv.fv_name
  // | Tm_PureApp head _ _ -> print_head head
  | _ -> "<pure term>"


let rec print_skel (t:st_term) = 
  match t.term with
  | Tm_Abs { body }  -> Printf.sprintf "(fun _ -> %s)" (print_skel body)
  | Tm_Protect { t=p } -> Printf.sprintf "(Protect %s)" (print_skel p)
  | Tm_Return { term = p } -> print_head p
  | Tm_Bind { head=e1; body=e2 } -> Printf.sprintf "(Bind %s %s)" (print_skel e1) (print_skel e2)
  | Tm_TotBind { body=e2 } -> Printf.sprintf "(TotBind _ %s)" (print_skel e2)
  | Tm_If _ -> "If"
  | Tm_While _ -> "While"
  | Tm_Admit _ -> "Admit"
  | Tm_Par _ -> "Par"
  | Tm_Rewrite _ -> "Rewrite"
  | Tm_WithLocal _ -> "WithLocal"
  | Tm_STApp { head = p } -> print_head p
  | Tm_IntroExists _ -> "IntroExists"
  | Tm_ElimExists _ -> "ElimExists"

  
let check_par
  (allow_inst:bool)
  (g:env)
  (t:st_term{Tm_Par? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  (check':bool -> check_t)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c) =
  let g = push_context "check_par" g in
  let Tm_Par {pre1=preL; body1=eL; post1=postL;
              pre2=preR; body2=eR; post2=postR} = t.term in
  let (| preL, preL_typing |) =
    check_term_with_expected_type g preL Tm_VProp in
  let (| preR, preR_typing |) =
    check_term_with_expected_type g preR Tm_VProp in

  let postL_hint = Checker.Common.intro_post_hint g None postL in
  let (| eL, cL, eL_typing |) =
    check' allow_inst g eL preL (E preL_typing) (Some postL_hint) in

  // TODO: can we avoid checking cL and cR?

  if C_ST? cL
  then
    let cL_typing = check_comp g cL (E preL_typing) in
    let postR_hint = Checker.Common.intro_post_hint g None postR in
    let (| eR, cR, eR_typing |) =
      check' allow_inst g eR preR (E preR_typing) (Some postR_hint) in

    if C_ST? cR && eq_univ (comp_u cL) (comp_u cR)
    then
      let cR_typing = check_comp g cR (E preR_typing) in
      let x = fresh g in
      let d = T_Par _ _ _ _ _ x cL_typing cR_typing eL_typing eR_typing in
      repack (try_frame_pre pre_typing d) post_hint true
    else T.fail "par: cR is not stt"
  else T.fail "par: cL is not stt"

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
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c) =
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
           if not (C_ST? c_body && ///these next three checks should be excluded by a stronger type on check'
                   eq_tm (comp_post c_body) body_post.post &&
                   eq_tm (comp_res c_body) body_post.ret_ty &&
                   eq_univ (comp_u c_body) body_post.u)
           then T.fail "withlocal: body is not stt or postcondition mismatch"
           else let body = close_st_term opened_body x in
                assume (open_st_term (close_st_term opened_body x) x == opened_body);
                let c = C_ST {u=comp_u c_body;res=comp_res c_body;pre;post=post.post} in
                let c_typing =
                    let post_typing_rec = Checker.Common.post_hint_typing g post x in
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

let check_rewrite
  (g:env)
  (t:st_term{Tm_Rewrite? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c) =
  let g = push_context "check_rewrite" g in
  let Tm_Rewrite {t1=p; t2=q} = t.term in
  let (| p, p_typing |) = check_vprop g p in
  let (| q, q_typing |) = check_vprop g q in
  let equiv_p_q =
      if eq_tm p q
      then VE_Refl g p
      else match T.check_equiv (elab_env g) (elab_term p) (elab_term q) with
           | None, issues -> 
             T.fail (Printf.sprintf "rewrite: p and q elabs are not equiv\n%s" 
                          (Pulse.Checker.Pure.print_issues g issues))
           | Some token, _ -> VE_Ext g p q token in
	     let d = T_Rewrite _ p q p_typing equiv_p_q in
	     repack (try_frame_pre pre_typing d) post_hint true

#push-options "--query_stats"
let rec check' : bool -> check_t =
  fun (allow_inst:bool)
    (g:env)
    (t:st_term)
    (pre:term)
    (pre_typing: tot_typing g pre Tm_VProp)
    (post_hint:post_hint_opt g) ->
  let open T in
  // T.print (Printf.sprintf "At %s: allow_inst: %s, context: %s, term: %s\n"
  //            (T.range_to_string t.range)
  //            (string_of_bool allow_inst)
  //            (Pulse.Syntax.Printer.term_to_string pre)
  //            (Pulse.Syntax.Printer.st_term_to_string t));
  let t : st_term = //weird, remove the annotation and get a strange failure
    if allow_inst
    then auto_elims g pre t
    else t
  in
  T.print (Printf.sprintf "At %s: precondition is %s\n"
                          (T.range_to_string t.range)
                          (Pulse.Syntax.Printer.term_to_string pre));
  let g = push_context (tag_of_st_term t) g in
  try 
    match t.term with
    | Tm_Protect _ -> T.fail "Protect should have been removed"

    // | Tm_Return {term = Tm_Bvar _} -> T.fail "not locally nameless"
    | Tm_Return _ ->
      check_return allow_inst g t pre pre_typing post_hint
  
    | Tm_Abs _ ->
      check_abs g t pre pre_typing post_hint (check' true)

    | Tm_STApp _ ->
      check_stapp allow_inst g t pre pre_typing post_hint check'

    | Tm_Bind _ ->
      check_bind g t pre pre_typing post_hint (check' true)

    | Tm_TotBind _ ->
      check_tot_bind g t pre pre_typing post_hint (check' true)

    | Tm_If { b; then_=e1; else_=e2; post=post_if } ->
      let post =
        match post_if, post_hint with
        | None, Some p -> p
        | Some p, None ->
          Checker.Common.intro_post_hint g None p
        | _, _ -> T.fail "Either two annotations for if post or none"
      in
      check_if g b e1 e2 pre pre_typing post (check' true)

    | Tm_ElimExists _ ->
      check_elim_exists g t pre pre_typing post_hint

    | Tm_IntroExists { witnesses } ->
      let should_infer_witnesses =
        match witnesses with
        | [w] -> (
          match w with
          | Tm_Unknown -> true
          | _ -> false
        )
        | _ -> true
      in
      if should_infer_witnesses
      then (
        let unary_intros = maybe_infer_intro_exists g t pre in
        // T.print (Printf.sprintf "Inferred unary_intros:\n%s\n"
        //                         (P.st_term_to_string unary_intros));
        check' allow_inst g unary_intros pre pre_typing post_hint
      )
      else (
        check_intro_exists_either g t None pre pre_typing post_hint
      )

    | Tm_While _ ->
      check_while allow_inst g t pre pre_typing post_hint check'

    | Tm_Admit _ ->
      check_admit g t pre pre_typing post_hint

    | Tm_Par _ ->
      check_par allow_inst g t pre pre_typing post_hint check'

    | Tm_WithLocal _ ->
      check_withlocal allow_inst g t pre pre_typing post_hint check'

    | Tm_Rewrite _ ->
      check_rewrite g t pre pre_typing post_hint
  with
  | Framing_failure failure ->
    handle_framing_failure g t pre pre_typing post_hint failure (check' true)
  | e -> T.raise e

let check = check' true
