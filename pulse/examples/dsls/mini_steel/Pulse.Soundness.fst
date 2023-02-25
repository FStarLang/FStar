module Pulse.Soundness
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common
module Bind = Pulse.Soundness.Bind
module Lift = Pulse.Soundness.Lift
module Frame = Pulse.Soundness.Frame
module STEquiv = Pulse.Soundness.STEquiv
module Return = Pulse.Soundness.Return
module Exists = Pulse.Soundness.Exists
module While = Pulse.Soundness.While
module LN = Pulse.Typing.LN
module FV = Pulse.Typing.FV
module STT = Pulse.Soundness.STT

module Typing = Pulse.Typing
module EPure = Pulse.Elaborate.Pure

let soundness_t (d:'a) = 
    f:stt_env ->
    g:env ->
    t:st_term ->
    c:comp ->
    d':st_typing f g t c{d' << d} ->
    GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d')
                    (elab_comp c))

let tabs_t (d:'a) = 
    #f:stt_env ->
    #g:env ->
    #u:universe ->
    #ty:term ->
    q:option qualifier ->
    ppname:ppname ->
    t_typing:tot_typing f g ty (Tm_Type u) { t_typing << d } ->
    #body:st_term ->
    #x:var { None? (lookup g x) /\ ~(x `Set.mem` freevars_st body) } ->
    #c:comp ->
    body_typing:st_typing f ((x, Inl ty)::g) (open_st_term body x) c { body_typing << d } ->
    GTot (RT.typing (extend_env_l f g)
                    (mk_abs_with_name ppname (elab_term ty) (elab_qual q) (RT.close_term (elab_st_typing body_typing) x))
                      (elab_term (Tm_Arrow {binder_ty=ty;binder_ppname=ppname} q (close_comp c x))))

let lift_soundness
  (f:stt_env)
  (g:env)
  (t:st_term)
  (c:comp)
  (d:st_typing f g t c{T_Lift? d})
  (soundness:soundness_t d)
  : GTot (RT.typing (extend_env_l f g) (elab_st_typing d) (elab_comp c)) =
  LN.st_typing_ln d;
  let T_Lift _ e c1 c2 e_typing lc = d in
  LN.st_typing_ln e_typing;
  match lc with
  | Lift_STAtomic_ST _ _ ->
    Lift.elab_lift_stt_atomic_typing f g
      c1 c2 _ (soundness _ _ _ _ e_typing) lc
  | Lift_STGhost_STAtomic _ _ w ->
    let (| reveal_a, reveal_a_typing |) = w in
    Lift.elab_lift_stt_ghost_typing f g
      c1 c2 _ (soundness _ _ _ _ e_typing) lc
      _ (tot_typing_soundness reveal_a_typing)

let frame_soundness
  (f:stt_env)
  (g:env)
  (t:st_term)
  (c:comp)
  (d:st_typing f g t c{T_Frame? d})
  (soundness:soundness_t d)
  : GTot (RT.typing (extend_env_l f g) (elab_st_typing d) (elab_comp c)) =

  let T_Frame _ e c frame frame_typing e_typing = d in
  let r_e_typing = soundness _ _ _ _ e_typing in
  LN.st_typing_ln e_typing;
  Frame.elab_frame_typing f g _ _ frame frame_typing r_e_typing

let stapp_soundness
  (f:stt_env)
  (g:env)
  (t:st_term)
  (c:comp)
  (d:st_typing f g t c{T_STApp? d})
  (soundness:soundness_t d)
  : GTot (RT.typing (extend_env_l f g) (elab_st_typing d) (elab_comp c)) =

  let T_STApp _ head formal q res arg head_typing arg_typing = d in
  let r_head = elab_term head in
  let r_arg = elab_term arg in
  let r_head_typing
    : RT.typing _ r_head (elab_term (Tm_Arrow {binder_ty=formal;binder_ppname=RT.pp_name_default} q res))
    = tot_typing_soundness head_typing
  in
  let r_arg_typing = tot_typing_soundness arg_typing in
  elab_comp_open_commute res arg;
  RT.T_App _ _ _ (binder_of_t_q_s (elab_term formal) (elab_qual q) RT.pp_name_default)
                 (elab_comp res)
                 r_head_typing
                 r_arg_typing

let stequiv_soundness
  (f:stt_env)
  (g:env)
  (t:st_term)
  (c:comp)
  (d:st_typing f g t c{T_Equiv? d})
  (soundness:soundness_t d)            
  : GTot (RT.typing (extend_env_l f g) (elab_st_typing d) (elab_comp c)) =

  let T_Equiv _ e c c' e_typing equiv = d in
  LN.st_typing_ln d;
  LN.st_typing_ln e_typing;
  let r_e_typing = soundness _ _ _ _ e_typing in 
  STEquiv.st_equiv_soundness _ _ _ _ equiv _ r_e_typing


#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 30"

let bind_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_Bind? d})
  (soundness: soundness_t d)
  (mk_t_abs: tabs_t d)
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c))
  = let T_Bind _ e1 e2 c1 c2 x c e1_typing t_typing e2_typing bc = d in
    LN.st_typing_ln e1_typing;
    LN.st_typing_ln e2_typing;      
    FV.st_typing_freevars_inv e1_typing x;
    let r1_typing
      : RT.typing _ _ (elab_comp c1)
      = soundness _ _ _ _ e1_typing
    in
    let r2_typing
      : RT.typing _ _ (elab_term (Tm_Arrow (null_binder (comp_res c1)) None (close_comp c2 x)))
      = mk_t_abs None _ t_typing e2_typing
    in
    match bc with
    | Bind_comp _ _ _ _ t2_typing y post2_typing ->
         Bind.elab_bind_typing f g _ _ _ x _ r1_typing _ r2_typing bc 
                               (tot_typing_soundness t2_typing)
                               (mk_t_abs_tot _ _ _ t2_typing post2_typing)
                               
    | Bind_comp_ghost_l _ _ _ _ (| reveal_a, reveal_a_typing |) t2_typing y post2_typing ->
         Bind.elab_bind_ghost_l_typing f g _ _ _ x _ r1_typing
           _ r2_typing bc
           (tot_typing_soundness t2_typing)
           (mk_t_abs_tot _ _ _ t2_typing post2_typing)
           (elab_term reveal_a)
           (tot_typing_soundness reveal_a_typing)
    | Bind_comp_ghost_r _ _ _ _ (| reveal_b, reveal_b_typing |) t2_typing y post2_typing ->
         Bind.elab_bind_ghost_r_typing f g _ _ _ x _ r1_typing
           _ r2_typing bc
           (tot_typing_soundness t2_typing)
           (mk_t_abs_tot _ _ _ t2_typing post2_typing)
           (elab_term reveal_b)
           (tot_typing_soundness reveal_b_typing)
#pop-options

let intro_exists_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_IntroExists? d})
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let t0 = t in
  let T_IntroExists _ u t p e t_typing p_typing e_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let rp = elab_term p in
  let re = elab_term e in

  let rt_typing : RT.typing _ rt (R.pack_ln (R.Tv_Type ru)) =
    tot_typing_soundness t_typing in

  let rp_typing
    : RT.typing _
        (mk_exists ru rt (mk_abs rt R.Q_Explicit rp)) vprop_tm =
    tot_typing_soundness p_typing in
  let rp_typing
    : RT.typing _
        (mk_abs rt R.Q_Explicit rp)
        (mk_arrow (rt, R.Q_Explicit) vprop_tm) =
    Exists.exists_inversion rp_typing in

  let re_typing : RT.typing _ re rt =
    tot_typing_soundness e_typing in

  assume (R.pack_ln (R.Tv_App (mk_abs rt R.Q_Explicit rp) (re, R.Q_Explicit)) ==
          RT.open_or_close_term' rp (RT.OpenWith re) 0);

  elab_open_commute' p e 0;
  assert (elab_term (open_term' p e 0) ==
          R.pack_ln (R.Tv_App (mk_abs rt R.Q_Explicit rp) (re, R.Q_Explicit)));

  Exists.intro_exists_soundness rt_typing rp_typing re_typing

assume val freevars_not_mem_close (t:R.term) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (RT.freevars t)))
      (ensures RT.open_or_close_term' t (RT.CloseVar x) i == t)

#push-options "--z3rlimit_factor 4"
let elim_exists_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_ElimExists? d})
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_ElimExists _ u t p x t_typing p_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let rp = elab_term p in
  let rt_typing = tot_typing_soundness t_typing in
  let rp_typing
    : RT.typing (extend_env_l f g)
                (mk_exists ru (elab_term t)
                   (mk_abs (elab_term t) R.Q_Explicit (elab_term p)))
                vprop_tm
    = tot_typing_soundness p_typing in
  let rp_typing = Exists.exists_inversion rp_typing in

  FV.st_typing_freevars_inv d x;
  assert (~ (Set.mem x (freevars t)));
  assert (~ (Set.mem x (freevars p)));

  let x_tm = Tm_Var {nm_index=x;nm_ppname=RT.pp_name_default} in
  let rx_tm = R.pack_ln (R.Tv_Var (R.pack_bv (RT.make_bv x tun))) in
  let rx_bv = R.pack_ln (R.Tv_BVar (R.pack_bv (RT.make_bv 0 tun))) in
  assert (elab_term (mk_reveal u t x_tm) ==
          EPure.mk_reveal ru rt rx_tm);
  calc (==) {
    elab_term (close_term' (open_term' p (mk_reveal u t x_tm) 0) x 0);
       (==) { elab_close_commute'
                (open_term' p (mk_reveal u t x_tm) 0)
                x
                0 }
    RT.open_or_close_term' (elab_term (open_term' p (mk_reveal u t x_tm) 0)) (RT.CloseVar x) 0;
       (==) { elab_open_commute'
                p
                (mk_reveal u t x_tm)
                0 }
    RT.open_or_close_term' (RT.open_or_close_term' rp (RT.OpenWith (EPure.mk_reveal ru rt rx_tm)) 0) (RT.CloseVar x) 0;
       (==) {
               assume (R.pack_ln (R.Tv_App (mk_abs rt R.Q_Explicit rp) (EPure.mk_reveal ru rt rx_tm, R.Q_Explicit)) ==
                       RT.open_or_close_term' rp (RT.OpenWith (EPure.mk_reveal ru rt rx_tm)) 0)
            }
    RT.open_or_close_term' (R.pack_ln (R.Tv_App (mk_abs rt R.Q_Explicit rp) (EPure.mk_reveal ru rt rx_tm, R.Q_Explicit))) (RT.CloseVar x) 0;
       (==) { 
              EPure.elab_freevars_inverse t;
              EPure.elab_freevars_inverse p;
              freevars_not_mem_close rt x 0;
              freevars_not_mem_close rp x 1
            }
    R.pack_ln (R.Tv_App (mk_abs rt R.Q_Explicit rp)
                        (EPure.mk_reveal ru rt rx_bv, R.Q_Explicit));
       (==) { }
    Exists.elim_exists_post_body ru rt (mk_abs rt R.Q_Explicit rp);
  };
  Exists.elim_exists_soundness rt_typing rp_typing
#pop-options

#push-options "--z3rlimit_factor 4 --query_stats"
let while_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_While? d})
  (soundness: soundness_t d)
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_While _ inv cond body inv_typing cond_typing body_typing = d in
  let rinv = mk_abs bool_tm R.Q_Explicit (elab_term inv) in
  let rinv_typing
    : RT.typing _
        (mk_exists uzero bool_tm rinv)
        vprop_tm =
    tot_typing_soundness inv_typing in
  let rinv_typing
    : RT.typing _
        rinv
        (mk_arrow (bool_tm, R.Q_Explicit) vprop_tm) =
    Exists.exists_inversion rinv_typing in
  let rcond_typing
    : RT.typing _ (elab_st_typing cond_typing)
        (mk_stt_comp uzero bool_tm (mk_exists uzero bool_tm rinv) rinv) =
    soundness f g cond (comp_while_cond inv) cond_typing in

  elab_open_commute' inv tm_true 0;
  assume (R.pack_ln (R.Tv_App (mk_abs bool_tm R.Q_Explicit (elab_term inv)) (true_tm, R.Q_Explicit)) ==
          RT.open_or_close_term' (elab_term inv) (RT.OpenWith true_tm) 0);

  let rbody_typing
    : RT.typing _ (elab_st_typing body_typing)
        (mk_stt_comp uzero unit_tm
           (R.pack_ln (R.Tv_App rinv (true_tm, R.Q_Explicit)))
           (mk_abs unit_tm R.Q_Explicit (mk_exists uzero bool_tm rinv))) =
    soundness f g body (comp_while_body inv) body_typing in

  elab_open_commute' inv tm_false 0;
  assume (R.pack_ln (R.Tv_App (mk_abs bool_tm R.Q_Explicit (elab_term inv)) (false_tm, R.Q_Explicit)) ==
          RT.open_or_close_term' (elab_term inv) (RT.OpenWith false_tm) 0);

  While.while_soundness rinv_typing rcond_typing rbody_typing


#push-options "--z3rlimit_factor 4"
let if_soundness
  (f:stt_env)
  (g:env)
  (t:st_term)
  (c:comp)
  (d:st_typing f g t c{T_If? d})
  (soundness:soundness_t d)
  (ct_soundness: (f:stt_env -> g:env -> c:comp -> uc:universe ->
                  d':comp_typing f g c uc{d' << d} ->
              GTot (RT.typing (extend_env_l f g)
                              (elab_comp c)
                              (RT.tm_type (elab_universe uc)))))
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_If _ b e1 e2  _ u_c hyp b_typing e1_typing e2_typing (E c_typing) = d in
  let rb_typing : RT.typing (extend_env_l f g)
                            (elab_term b)
                            RT.bool_ty =
    tot_typing_soundness b_typing in
  let g_then = (hyp, Inl (mk_eq2 U_zero tm_bool b tm_true))::g in
  let re1_typing
    : RT.typing (RT.extend_env (extend_env_l f g)
                               hyp
                               (RT.eq2 (R.pack_universe R.Uv_Zero)
                                       RT.bool_ty
                                       (elab_term b)
                                       RT.true_bool))
                (elab_st_typing e1_typing)
                (elab_comp c) =
    soundness f g_then e1 c e1_typing in
  let g_else = (hyp, Inl (mk_eq2 U_zero tm_bool b tm_false))::g in
  let re2_typing
    : RT.typing (RT.extend_env (extend_env_l f g)
                               hyp
                               (RT.eq2 (R.pack_universe R.Uv_Zero)
                                       RT.bool_ty
                                       (elab_term b)
                                       RT.false_bool))
                (elab_st_typing e2_typing)
                (elab_comp c) =
    soundness f g_else e2 c e2_typing in
  let c_typing = 
    ct_soundness _ _ _ _ c_typing
  in
  assume (~(hyp `Set.mem` RT.freevars (elab_st_typing e1_typing)));
  assume (~(hyp `Set.mem` RT.freevars (elab_st_typing e2_typing)));  
  RT.T_If _ _ _ _ _ _ _ rb_typing re1_typing re2_typing c_typing
#pop-options

#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 10"

let comp_typing_soundness (f:stt_env)
                          (g:env)
                          (c:comp)
                          (uc:universe)
                          (d:comp_typing f g c uc)
                          (soundness:soundness_t d)
  : GTot (RT.typing (extend_env_l f g) (elab_comp c) (RT.tm_type (elab_universe uc)))
         (decreases d)
  = let stc_soundness (st:_) (d_st:st_comp_typing f g st { d_st << d }) 
      : GTot (RT.typing (extend_env_l f g) (elab_term st.res) (RT.tm_type (elab_universe st.u)) &
              RT.typing (extend_env_l f g) (elab_term st.pre) vprop_tm &
              RT.typing (extend_env_l f g) (mk_abs (elab_term st.res) R.Q_Explicit
                                                   (elab_term st.post))
                                           (post1_type_bind (elab_term st.res)))
      = let STC _ st x dres dpre dpost = d_st in
        let res_typing = tot_typing_soundness dres in
        let pre_typing = tot_typing_soundness dpre in      
        calc (==) {
          RT.close_term (elab_term (open_term st.post x)) x;
        (==) { elab_open_commute st.post x }
          RT.close_term (RT.open_term (elab_term st.post) x) x;
        (==) { 
               elab_freevars_inverse st.post;
               RT.close_open_inverse (elab_term st.post) x
             }
          elab_term st.post;
        };
        let post_typing  = mk_t_abs_tot f g RT.pp_name_default dres dpost in
        res_typing, pre_typing, post_typing
    in
    match d with
    | CT_Tot _ t _ dt ->
      tot_typing_soundness dt
      
    | CT_ST _ st d_st -> 
      let res_typing, pre_typing, post_typing = stc_soundness st d_st in
      STT.stt_typing res_typing pre_typing post_typing

    | CT_STAtomic _ i st d_i d_st -> 
      let i_typing = tot_typing_soundness d_i in
      let res_typing, pre_typing, post_typing = stc_soundness st d_st in
      STT.stt_atomic_typing res_typing i_typing pre_typing post_typing

    | CT_STGhost _ i st d_i d_st -> 
      let i_typing = tot_typing_soundness d_i in
      let res_typing, pre_typing, post_typing = stc_soundness st d_st in
      STT.stt_ghost_typing res_typing i_typing pre_typing post_typing
#pop-options

#push-options "--query_stats --fuel 2 --ifuel 2"
let rec soundness (f:stt_env)
                  (g:env)
                  (t:st_term)
                  (c:comp)
                  (d:st_typing f g t c)
  : GTot (RT.typing (extend_env_l f g) (elab_st_typing d) (elab_comp c))
         (decreases d)
  = let mk_t_abs (#f:stt_env)
                 (#g:env)
                 (#u:universe)
                 (#ty:term)
                 (q:option qualifier)
                 (ppname:ppname)
                 (t_typing:tot_typing f g ty (Tm_Type u) { t_typing << d })
                 (#body:st_term)
                 (#x:var { None? (lookup g x) /\ ~(x `Set.mem` freevars_st body) })
                 (#c:comp)
                 (body_typing:st_typing f ((x, Inl ty)::g) (open_st_term body x) c { body_typing << d })
      : GTot (RT.typing (extend_env_l f g)
                        (mk_abs_with_name ppname (elab_term ty) (elab_qual q) (RT.close_term (elab_st_typing body_typing) x))
                        (elab_term (Tm_Arrow {binder_ty=ty;binder_ppname=ppname} q (close_comp c x))))
      = let E t_typing = t_typing in
        let r_t_typing = tot_typing_soundness (E t_typing) in
        let r_body_typing = soundness _ _ _ _ body_typing in
        mk_t_abs f g #_ #_ #_ #t_typing ppname r_t_typing r_body_typing
    in
    LN.st_typing_ln d;
    match d with
    | T_Lift _ _ _ _ _ _ ->
      lift_soundness _ _ _ _ d soundness
    | T_Frame _ _ _ _ _ _ ->
      frame_soundness _ _ _ _ d soundness

    | T_Tot _ _ _ d -> tot_typing_soundness d

    | T_Abs _ x q ty u body c t_typing body_typing ->
      mk_t_abs q RT.pp_name_default t_typing body_typing    

    | T_STApp _ _ _ _ _ _ _ _ ->
      stapp_soundness _ _ _ _ d soundness

    | T_Bind _ _e1 _e2 _c1 _c2 _x _c _e1_typing _t_typing _e2_typing _bc ->
      bind_soundness d soundness mk_t_abs

    | T_Equiv _ _ _ _ _ _ ->
      stequiv_soundness _ _ _ _ d soundness

    | T_Return _ e t u e_typing t_typing ->
      Return.elab_return_typing t_typing e_typing

    | T_ReturnNoEq _ e t u e_typing t_typing ->
      let e_typing = soundness _ _ _ _ e_typing in
      Return.elab_return_noeq_typing t_typing e_typing

    | T_If _ _ _ _ _ _ _ _ _ _ _->
      let ct_soundness f g c uc (d':_ {d' << d}) =
        comp_typing_soundness f g c uc d' soundness
      in
      if_soundness _ _ _ _ d soundness ct_soundness

    | T_ElimExists _ _ _ _ _ _ _ ->
      elim_exists_soundness d
    | T_IntroExists _ _ _ _ _ _ _ _ ->
      intro_exists_soundness d

    | T_While _ _ _ _ _ _ _ ->
      while_soundness d soundness
#pop-options

let soundness_lemma
  (f:stt_env)
  (g:env)
  (t:st_term)
  (c:comp)
  (d:st_typing f g t c)
  : Lemma (ensures RT.typing (extend_env_l f g)
                             (elab_st_typing d)
                             (elab_comp c))
  = FStar.Squash.bind_squash
      #(st_typing f g t c)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness f g t c d))
