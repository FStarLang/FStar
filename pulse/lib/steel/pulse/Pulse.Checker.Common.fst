module Pulse.Checker.Common
module T = FStar.Tactics
module Metatheory = Pulse.Typing.Metatheory
module CP = Pulse.Checker.Pure
module RU = Pulse.RuntimeUtils
module FV = Pulse.Typing.FV
module P = Pulse.Syntax.Printer

let post_hint_typing g p x = {
  ty_typing=admit();
  post_typing=admit()
}

let post_typing_as_abstraction (#g:env) (#x:var) (#ty:term) (#t:term { Metatheory.fresh_wrt x g (freevars t) })
                               (_:tot_typing (push_binding g x ty) (open_term t x) Tm_VProp)
  : FStar.Ghost.erased (RT.tot_typing (elab_env g) (mk_abs ty t) (mk_arrow ty Tm_VProp))                                 
  = admit()

let intro_post_hint g ret_ty_opt post =
  let x = fresh g in
  let ret_ty = 
      match ret_ty_opt with
      | None -> Tm_FStar RT.unit_ty FStar.Range.range_0
      | Some t -> t
  in
  let ret_ty, _ = CP.instantiate_term_implicits g ret_ty in
  let (| u, ty_typing |) = CP.check_universe g ret_ty in
  let (| post, post_typing |) = CP.check_vprop (push_binding g x ret_ty) (open_term_nv post (v_as_nv x)) in 
  let post' = close_term post x in
  Pulse.Typing.FV.freevars_close_term post x 0;
  assume (open_term post' x == post);
  { g; ret_ty; u; ty_typing; post=post'; post_typing=post_typing_as_abstraction #_ #_ #_ #post' post_typing }



let post_hint_from_comp_typing #g #c ct = 
  let st_comp_typing = Metatheory.comp_typing_inversion ct in
  let (| ty_typing, pre_typing, x, post_typing |) = Metatheory.st_comp_typing_inversion st_comp_typing in
  let p : post_hint_t = 
    { g; ret_ty = comp_res c; u=comp_u c; 
      ty_typing=ty_typing;
      post=comp_post c;
      post_typing=post_typing_as_abstraction post_typing }
  in
  p

let try_frame_pre (#g:env)
                  (#t:st_term)
                  (#pre:term)
                  (pre_typing: tot_typing g pre Tm_VProp)
                  (#c:comp_st)
                  (t_typing: st_typing g t c)
  : T.Tac (c':comp_st { comp_pre c' == pre } &
           st_typing g t c')
  = let g = CP.push_context "try_frame_pre" t.range g in
    if RU.debug_at_level (fstar_env g) "try_frame"
    then T.print (Printf.sprintf "(Try frame@%s) with %s\n\tcomp=%s,\n\tpre=%s\n"
                                 (T.range_to_string t.range)
                                 (print_context g)
                                 (P.comp_to_string c)
                                 (P.term_to_string pre));
    match Pulse.Checker.Framing.try_frame_pre #g pre_typing t_typing with
    | Inl ok -> ok
    | Inr fail -> T.raise (Framing_failure fail)

#push-options "--z3rlimit_factor 2"
let replace_equiv_post
      (r:range)
      (g:env)
      (c:comp{stateful_comp c /\ freevars_comp c `Set.subset` FV.vars_of_env g})
      (ct:Metatheory.comp_typing_u g c)
      (post_hint:post_hint_opt g)
  : T.Tac (c1:comp { stateful_comp c1 /\ comp_pre c1 == comp_pre c /\ comp_post_matches_hint c1 post_hint } &
           st_equiv g c c1)
  = let g = CP.push_context "replace_equiv_post" r g in
    let {u=u_c;res=res_c;pre=pre_c;post=post_c} = st_comp_of_comp c in
    let st_typing = Metatheory.comp_typing_inversion ct in
    let (| res_c_typing, pre_c_typing, x, post_c_typing |) = Metatheory.st_comp_typing_inversion st_typing in
    let px = v_as_nv x in
    let g_post = push_binding g x res_c in
    let post_c_opened = open_term_nv post_c px in
    match post_hint with
    | None ->
      (| c,
         ST_VPropEquiv
           g c c x pre_c_typing res_c_typing post_c_typing
           (VE_Refl _ _)
           (VE_Refl _ _) |)
    | Some post ->
      if not (eq_univ u_c post.u &&
              eq_tm res_c post.ret_ty)
      then fail g None 
            (Printf.sprintf "(%s) Inferred result type does not match annotation.\n\
                             Expected type %s\n\
                             Got type %s\n"
                  (T.range_to_string r)
                  (P.term_to_string post.ret_ty)
                  (P.term_to_string res_c))
      else if (x `Set.mem` freevars post.post)
      then fail g None "Unexpected variable clash with annotated postcondition"
      else (
        let post_opened = open_term_nv post.post px in
        let post_c_post_eq
          : vprop_equiv g_post post_c_opened post_opened
          = Pulse.Checker.Framing.check_vprop_equiv
              (CP.push_context "check_vprop_equiv" r g_post)
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
        assume (close_term post_opened x == post.post);
        assume (open_term (close_term post_opened x) x == post_opened);
        (| c_with_post,
           ST_VPropEquiv
             g c c_with_post x pre_c_typing res_c_typing post_c_typing
             (VE_Refl _ _)
             post_c_post_eq |)
      )
#pop-options

let repack (#g:env) (#pre:term) (#t:st_term)
           (x:(c:comp_st { comp_pre c == pre } & st_typing g t c))
           (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint)
  = let (| c, d_c |) = x in
    if stateful_comp c
    then (
      FV.st_typing_freevars d_c;
      let (| c1, c_c1_eq |) = replace_equiv_post t.range g c (Metatheory.st_typing_correctness d_c) post_hint in
      (| t, c1, T_Equiv _ _ _ _ d_c c_c1_eq |)
    )
    else (| t, c, d_c |)

let intro_comp_typing (g:env) 
                      (c:comp_st)
                      (pre_typing:tot_typing g (comp_pre c) Tm_VProp)
                      (res_typing:universe_of g (comp_res c) (comp_u c))
                      (x:var { Metatheory.fresh_wrt x g (freevars (comp_post c)) })
                      (post_typing:tot_typing (push_binding g x (comp_res c)) (open_term (comp_post c) x) Tm_VProp)
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
      let (| ty, i_typing |) = CP.core_check_term g i in
      if not (eq_tm ty Tm_Inames)
      then fail g None "Ill-typed inames"
      else CT_STAtomic _ _ _ (E i_typing) stc
    | C_STGhost i st -> 
      let stc = intro_st_comp_typing st in
      let (| ty, i_typing |) = CP.core_check_term g i in
      if not (eq_tm ty Tm_Inames)
      then fail g None "Ill-typed inames"
      else CT_STGhost _ _ _ (E i_typing) stc
