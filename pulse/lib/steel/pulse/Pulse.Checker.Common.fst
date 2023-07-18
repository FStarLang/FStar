module Pulse.Checker.Common
module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing
module Metatheory = Pulse.Typing.Metatheory
module CP = Pulse.Checker.Pure
module RU = Pulse.RuntimeUtils
module FV = Pulse.Typing.FV
module P = Pulse.Syntax.Printer

let format_failed_goal (g:env) (ctxt:list term) (goal:list term) =
  let terms_to_strings (ts:list term)= T.map Pulse.Syntax.Printer.term_to_string ts in
  let numbered_list ss = 
       let _, s = T.fold_left (fun (i, acc) s -> (i+1, Printf.sprintf "%d. %s" i s :: acc)) (1, []) ss in
       String.concat "\n  " (List.rev s)
  in
  let format_terms (ts:list term) = numbered_list (terms_to_strings ts) in
  Printf.sprintf 
    "Failed to prove the following goals:\n  \
     %s\n\
     The remaining conjuncts in the separation logic context available for use are:\n  \
     %s\n\
     The typing context is:\n  \
     %s\n"
    (format_terms goal)
    (format_terms ctxt)
    (env_to_string g)


let mk_arrow ty t = RT.mk_arrow (elab_term ty) T.Q_Explicit (elab_term t)
let mk_abs ty t = RT.(mk_abs (elab_term ty) T.Q_Explicit (elab_term t))

let post_typing_as_abstraction (#g:env) (#x:var) (#ty:term) (#t:term { fresh_wrt x g (freevars t) })
                               (_:tot_typing (push_binding g x ppname_default ty) (open_term t x) tm_vprop)
  : FStar.Ghost.erased (RT.tot_typing (elab_env g) (mk_abs ty t) (mk_arrow ty tm_vprop))                                 
  = admit()

let intro_post_hint g ret_ty_opt post =
  let x = fresh g in
  let ret_ty = 
      match ret_ty_opt with
      | None -> tm_fstar RT.unit_ty FStar.Range.range_0
      | Some t -> t
  in
  let ret_ty, _ = CP.instantiate_term_implicits g ret_ty in
  let (| u, ty_typing |) = CP.check_universe g ret_ty in
  let (| post, post_typing |) = CP.check_vprop (push_binding g x ppname_default ret_ty) (open_term_nv post (v_as_nv x)) in 
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
                  (pre_typing: tot_typing g pre tm_vprop)
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

let rec vprop_equiv_typing (#g:_) (#t0 #t1:term) (v:vprop_equiv g t0 t1)
  : GTot ((tot_typing g t0 tm_vprop -> tot_typing g t1 tm_vprop) &
          (tot_typing g t1 tm_vprop -> tot_typing g t0 tm_vprop))
        (decreases v)
  = match v with
    | VE_Refl _ _ -> (fun x -> x), (fun x -> x)

    | VE_Sym _ _ _ v' -> 
      let f, g = vprop_equiv_typing v' in
      g, f

    | VE_Trans g t0 t2 t1 v02 v21 ->
      let f02, f20 = vprop_equiv_typing v02 in
      let f21, f12 = vprop_equiv_typing v21 in
      (fun x -> f21 (f02 x)), 
      (fun x -> f20 (f12 x))

    | VE_Ctxt g s0 s1 s0' s1' v0 v1 ->
      let f0, f0' = vprop_equiv_typing v0 in
      let f1, f1' = vprop_equiv_typing v1 in      
      let ff (x:tot_typing g (tm_star s0 s1) tm_vprop)
        : tot_typing g (tm_star s0' s1') tm_vprop
        = let s0_typing = star_typing_inversion_l x in
          let s1_typing = star_typing_inversion_r x in
          let s0'_typing, s1'_typing = f0 s0_typing, f1 s1_typing in
          star_typing s0'_typing s1'_typing
      in
      let gg (x:tot_typing g (tm_star s0' s1') tm_vprop)
        : tot_typing g (tm_star s0 s1) tm_vprop
        = let s0'_typing = star_typing_inversion_l x in
          let s1'_typing = star_typing_inversion_r x in
          star_typing (f0' s0'_typing) (f1' s1'_typing)        
      in
      ff, gg

    | VE_Unit g t ->
      let fwd (x:tot_typing g (tm_star tm_emp t) tm_vprop)
        : tot_typing g t tm_vprop
        = let r = star_typing_inversion_r x in
          r
      in
      let bk (x:tot_typing g t tm_vprop)
        : tot_typing g (tm_star tm_emp t) tm_vprop
        = star_typing emp_typing x
      in
      fwd, bk

    | VE_Comm g t0 t1 ->
      let f t0 t1 (x:tot_typing g (tm_star t0 t1) tm_vprop)
        : tot_typing g (tm_star t1 t0) tm_vprop
        = let tt0 = star_typing_inversion_l x in
          let tt1 = star_typing_inversion_r x in
          star_typing tt1 tt0
      in
      f t0 t1, f t1 t0

    | VE_Assoc g t0 t1 t2 ->
      let fwd (x:tot_typing g (tm_star t0 (tm_star t1 t2)) tm_vprop)
        : tot_typing g (tm_star (tm_star t0 t1) t2) tm_vprop
        = let tt0 = star_typing_inversion_l x in
          let tt12 = star_typing_inversion_r x in
          let tt1 = star_typing_inversion_l tt12 in
          let tt2 = star_typing_inversion_r tt12 in
          star_typing (star_typing tt0 tt1) tt2
      in
      let bk (x : tot_typing g (tm_star (tm_star t0 t1) t2) tm_vprop)
        : tot_typing g (tm_star t0 (tm_star t1 t2)) tm_vprop
        = let tt01 = star_typing_inversion_l x in
          let tt2 = star_typing_inversion_r x in
          let tt0 = star_typing_inversion_l tt01 in
          let tt1 = star_typing_inversion_r tt01 in
          star_typing tt0 (star_typing tt1 tt2)
      in
      fwd, bk
   
    | VE_Ext g t0 t1 token ->
      let d1, d2 = vprop_eq_typing_inversion g t0 t1 token in
      (fun _ -> d2),
      (fun _ -> d1)


let k_elab_unit (g:env) (ctxt:term)
  : continuation_elaborator g ctxt g ctxt
  = fun p r -> r

let k_elab_trans
  (#g0:env) (#g1:env { g1 `env_extends` g0 }) (#g2:env { g2 `env_extends` g1 }) (#ctxt0 #ctxt1 #ctxt2:term)
  (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
  (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2
   = fun post_hint res -> k0 post_hint (k1 post_hint res)

let comp_st_with_post (c:comp_st) (post:term)
  : c':comp_st { st_comp_of_comp c' == ({ st_comp_of_comp c with post} <: st_comp) } =
  match c with
  | C_ST st -> C_ST { st with post }
  | C_STGhost i st -> C_STGhost i { st with post }
  | C_STAtomic i st -> C_STAtomic i {st with post}

let ve_unit_r g (p:term) : vprop_equiv g (tm_star p tm_emp) p = 
  VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _)

let st_equiv_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                  (post:term { freevars post `Set.subset` freevars (comp_post c)})
                  (veq: (x:var { fresh_wrt x g (freevars (comp_post c)) } ->
                         vprop_equiv (push_binding g x ppname_default (comp_res c)) 
                                     (open_term (comp_post c) x)
                                     (open_term post x)))
  : st_typing g t (comp_st_with_post c post)
  = let c' = comp_st_with_post c post in
    let (| u_of, pre_typing, x, post_typing |) = Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness d))) in
    let veq = veq x in
    let st_equiv : st_equiv g c c' =
        ST_VPropEquiv g c c' x pre_typing u_of post_typing (VE_Refl _ _) veq
    in
    T_Equiv _ _ _ _ d st_equiv

let simplify_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                  (post:term { comp_post c == tm_star post tm_emp})
  : st_typing g t (comp_st_with_post c post)
  = st_equiv_post d post (fun x -> ve_unit_r (push_binding g x ppname_default (comp_res c)) (open_term post x))

let simplify_lemma (c:comp_st) (c':comp_st) (post_hint:option post_hint_t)
  : Lemma
    (requires
        comp_post_matches_hint c post_hint /\
        comp_res c' == comp_res c /\
        comp_u c' == comp_u c /\
        comp_post c' == tm_star (comp_post c) tm_emp)
    (ensures comp_post_matches_hint (comp_st_with_post c' (comp_post c)) post_hint /\
             comp_pre (comp_st_with_post c' (comp_post c)) == comp_pre c')
  = () 

let frame_for_req_in_ctxt (g:env) (ctxt:term) (req:term)
   = (frame:term &
      tot_typing g frame tm_vprop &
      vprop_equiv g (tm_star req frame) ctxt)

let vprop_equiv_typing_bk (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_vprop)
                           (#p:_) (d:vprop_equiv g p ctxt)
  : tot_typing g p tm_vprop 
  = let _, bk = vprop_equiv_typing d in
    bk ctxt_typing


#push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 0"
let k_elab_equiv_continutation (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt #ctxt1 #ctxt2:term)
  (k:continuation_elaborator g1 ctxt g2 ctxt1)
  (d:vprop_equiv g2 ctxt1 ctxt2)
  : continuation_elaborator g1 ctxt g2 ctxt2 =
  fun post_hint res ->
  let framing_token : frame_for_req_in_ctxt g2 ctxt1 ctxt2 =
    let d : vprop_equiv g2 (tm_star ctxt2 tm_emp) ctxt1 = 
      VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Trans _ _ _ _ (VE_Unit _ _) (VE_Sym _ _ _ d)) in
      (| tm_emp, emp_typing, d |)
  in
  let (| st, c, st_d |) = res in
  if not (stateful_comp c) then k post_hint (| st, c, st_d |)
  else
    let (| _, pre_typing, _, _ |) =
      Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness st_d))) in
    let (| c', st_d' |) =
      Pulse.Checker.Framing.apply_frame (vprop_equiv_typing_bk pre_typing d) st_d framing_token in
    assert (comp_post c' == tm_star (comp_post c) tm_emp);
    let st_d' = simplify_post st_d' (comp_post c) in
    k post_hint (| st, _, st_d' |)
#pop-options

let vprop_equiv_typing_fwd (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_vprop)
                           (#p:_) (d:vprop_equiv g ctxt p)
  : tot_typing g p tm_vprop 
  = let fwd, _ = vprop_equiv_typing d in
    fwd ctxt_typing

#push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 0"
let k_elab_equiv_prefix
  (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt1 #ctxt2 #ctxt:term)
  (k:continuation_elaborator g1 ctxt1 g2 ctxt)
  (d:vprop_equiv g1 ctxt1 ctxt2)
  : continuation_elaborator g1 ctxt2 g2 ctxt =
  fun post_hint res ->
  let framing_token : frame_for_req_in_ctxt g1 ctxt2 ctxt1 = 
  let d = VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Trans _ _ _ _ (VE_Unit _ _) d) in
    (| tm_emp, emp_typing, d |)
  in
  let res = k post_hint res in
  let (| st, c, st_d |) = res in
  if not (stateful_comp c) then (| st, c, st_d |)
  else let (| _, pre_typing, _, _ |) =
         Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness st_d))) in
       let (| c', st_d' |) =
         Pulse.Checker.Framing.apply_frame
           (vprop_equiv_typing_fwd pre_typing d)
           st_d
           framing_token in
        simplify_lemma c c' post_hint;
        let c''  = comp_st_with_post c' (comp_post c) in
        let st_d' : st_typing g1 st c'' = simplify_post st_d' (comp_post c) in
        let res : st_typing_in_ctxt g1 ctxt2 post_hint = (| st, c'', st_d' |) in
        res
#pop-options

let k_elab_equiv
  (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt1 #ctxt1' #ctxt2 #ctxt2':term)                 
  (k:continuation_elaborator g1 ctxt1 g2 ctxt2)
  (d1:vprop_equiv g1 ctxt1 ctxt1')
  (d2:vprop_equiv g2 ctxt2 ctxt2')
  : continuation_elaborator g1 ctxt1' g2 ctxt2' =
  
  let k : continuation_elaborator g1 ctxt1 g2 ctxt2' =
    k_elab_equiv_continutation k d2 in
  let k : continuation_elaborator g1 ctxt1' g2 ctxt2' =
    k_elab_equiv_prefix k d1 in
  k

#push-options "--query_stats --fuel 2 --ifuel 2 --split_queries no --z3rlimit_factor 20"
let continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (tm_star ctxt (comp_pre c1)) tm_vprop)
  (x:var { None? (lookup g x) })
  : T.Tac (continuation_elaborator
             g (tm_star ctxt (comp_pre c1))
             (push_binding g x ppname_default (comp_res c1)) (tm_star (open_term (comp_post c1) x) ctxt)) =

  let pre1 = comp_pre c1 in
  let res1 = comp_res c1 in
  let post1 = comp_post c1 in
  let ctxt_typing = star_typing_inversion_l ctxt_pre1_typing in
  // let p_prop = Metatheory.pure_typing_inversion pure_typing in
  let v_eq = VE_Comm g ctxt pre1 in
  let framing_token : frame_for_req_in_ctxt g (tm_star ctxt pre1) pre1 = 
    (| ctxt, ctxt_typing, VE_Comm g pre1 ctxt  |)
  in
  let (| c1, e1_typing |) =
    Pulse.Checker.Framing.apply_frame ctxt_pre1_typing e1_typing framing_token in
  let (| u_of_1, pre_typing, _, _ |) =
    Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness e1_typing))) in
  let b = res1 in
  let g' = push_binding g x ppname_default b in
  
  let post1_opened = open_term_nv post1 (v_as_nv x) in
  let k : continuation_elaborator g (tm_star ctxt pre1) g' (tm_star post1_opened ctxt) =
    fun post_hint res ->
    let (| e2, c2, e2_typing |) = res in
    if not (stateful_comp c2) // || None? post_hint
    then T.fail "Unexpected non-stateful comp in continuation elaborate"
    else (
      let e2_typing : st_typing g' e2 c2 = e2_typing in
      let e2_closed = close_st_term e2 x in
      assume (open_st_term e2_closed x == e2);
      assert (comp_pre c1 == (tm_star ctxt pre1));
      assert (comp_post c1 == tm_star post1 ctxt);
      assert (comp_pre c2 == tm_star post1_opened ctxt);
      assert (open_term (comp_post c1) x == tm_star post1_opened (open_term ctxt x));
      // ctxt is well-typed, hence ln
      assume (open_term ctxt x == ctxt);
      assert (open_term (comp_post c1) x == comp_pre c2);
      // we closed e2 with x
      assume (~ (x `Set.mem` freevars_st e2_closed));
      if x `Set.mem` freevars (comp_post c2)
      then T.fail "Impossible"
      else (
        let t_typing, post_typing =
          Pulse.Typing.Combinators.bind_res_and_post_typing g (st_comp_of_comp c2) x post_hint in
        let (| e, c, e_typing |) =
          Pulse.Typing.Combinators.mk_bind
            g (tm_star ctxt pre1) 
            e1 e2_closed c1 c2 (v_as_nv x) e1_typing
            u_of_1 
            e2_typing
            t_typing
            post_typing
        in
        (| e, c, e_typing |)
      )
    )

  in
  k
#pop-options


// #push-options "--z3rlimit_factor 2"
// let replace_equiv_post
//       (r:range)
//       (g:env)
//       (c:comp{stateful_comp c /\ freevars_comp c `Set.subset` FV.vars_of_env g})
//       (ct:Metatheory.comp_typing_u g c)
//       (post_hint:post_hint_opt g)
//   : T.Tac (c1:comp { stateful_comp c1 /\ comp_pre c1 == comp_pre c /\ comp_post_matches_hint c1 post_hint } &
//            st_equiv g c c1)
//   = let g = CP.push_context "replace_equiv_post" r g in
//     let {u=u_c;res=res_c;pre=pre_c;post=post_c} = st_comp_of_comp c in
//     let st_typing = Metatheory.comp_typing_inversion ct in
//     let (| res_c_typing, pre_c_typing, x, post_c_typing |) = Metatheory.st_comp_typing_inversion st_typing in
//     let px = v_as_nv x in
//     let g_post = push_binding g x (fst px) res_c in
//     let post_c_opened = open_term_nv post_c px in
//     match post_hint with
//     | None ->
//       (| c,
//          ST_VPropEquiv
//            g c c x pre_c_typing res_c_typing post_c_typing
//            (VE_Refl _ _)
//            (VE_Refl _ _) |)
//     | Some post ->
//       if not (eq_univ u_c post.u &&
//               eq_tm res_c post.ret_ty)
//       then fail g None 
//             (Printf.sprintf "(%s) Inferred result type does not match annotation.\n\
//                              Expected type %s\n\
//                              Got type %s\n"
//                   (T.range_to_string r)
//                   (P.term_to_string post.ret_ty)
//                   (P.term_to_string res_c))
//       else if (x `Set.mem` freevars post.post)
//       then fail g None "Unexpected variable clash with annotated postcondition"
//       else (
//         let post_opened = open_term_nv post.post px in
//         let post_c_post_eq
//           : vprop_equiv g_post post_c_opened post_opened
//           = Pulse.Checker.Framing.check_vprop_equiv
//               (CP.push_context "check_vprop_equiv" r g_post)
//               post_c_opened
//               post_opened
//               post_c_typing
//         in
//         let st_comp_with_post : st_comp = {
//           u=u_c;
//           res=res_c;
//           pre=pre_c;
//           post=close_term post_opened x
//         } in
//         let c_with_post = c `with_st_comp` st_comp_with_post in
//         assume (close_term post_opened x == post.post);
//         assume (open_term (close_term post_opened x) x == post_opened);
//         (| c_with_post,
//            ST_VPropEquiv
//              g c c_with_post x pre_c_typing res_c_typing post_c_typing
//              (VE_Refl _ _)
//              post_c_post_eq |)
//       )
// #pop-options

// let repack (#g:env) (#pre:term) (#t:st_term)
//            (x:(c:comp_st { comp_pre c == pre } & st_typing g t c))
//            (post_hint:post_hint_opt g)
//   : T.Tac (checker_result_t g pre post_hint true)
//   = let (| c, d_c |) = x in
//     if stateful_comp c
//     then (
//       FV.st_typing_freevars d_c;
//       let (| c1, c_c1_eq |) = replace_equiv_post t.range g c (Metatheory.st_typing_correctness d_c) post_hint in
//       (| t, c1, T_Equiv _ _ _ _ d_c c_c1_eq |)
//     )
//     else (| t, c, d_c |)

let intro_comp_typing (g:env) 
                      (c:comp_st)
                      (pre_typing:tot_typing g (comp_pre c) tm_vprop)
                      (res_typing:universe_of g (comp_res c) (comp_u c))
                      (x:var { fresh_wrt x g (freevars (comp_post c)) })
                      (post_typing:tot_typing (push_binding g x ppname_default (comp_res c)) (open_term (comp_post c) x) tm_vprop)
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
      if not (eq_tm ty tm_inames)
      then fail g None "Ill-typed inames"
      else CT_STAtomic _ _ _ (E i_typing) stc
    | C_STGhost i st -> 
      let stc = intro_st_comp_typing st in
      let (| ty, i_typing |) = CP.core_check_term g i in
      if not (eq_tm ty tm_inames)
      then fail g None "Ill-typed inames"
      else CT_STGhost _ _ _ (E i_typing) stc
