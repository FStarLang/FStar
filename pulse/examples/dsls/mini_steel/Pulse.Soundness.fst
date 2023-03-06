module Pulse.Soundness
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
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
module Admit = Pulse.Soundness.Admit
module Par = Pulse.Soundness.Par
module LN = Pulse.Typing.LN
module FV = Pulse.Typing.FV
module STT = Pulse.Soundness.STT

module Typing = Pulse.Typing
module EPure = Pulse.Elaborate.Pure

let elab_open_commute' (e:term) (v:term) (n:index)
  : Lemma (ensures
             RT.open_or_close_term' (elab_term e) (RT.OpenWith (elab_term v)) n ==
             elab_term (open_term' e v n))
          [SMTPat (elab_term (open_term' e v n))] =

  elab_open_commute' e v n

let elab_close_commute' (e:term) (v:var) (n:index)
  : Lemma (RT.open_or_close_term' (elab_term e) (RT.CloseVar v) n ==
           elab_term (close_term' e v n))
          [SMTPat (elab_term (close_term' e v n))] =

  elab_close_commute' e v n

let elab_comp_close_commute (c:comp) (x:var)
  : Lemma (ensures elab_comp (close_comp c x) == RT.close_term (elab_comp c) x)
          [SMTPat (elab_comp (close_comp c x))] =

  elab_comp_close_commute c x

let elab_comp_open_commute (c:comp) (x:term)
  : Lemma (ensures elab_comp (open_comp_with c x) == RT.open_with (elab_comp c) (elab_term x))
          [SMTPat (elab_comp (open_comp_with c x))] =

  elab_comp_open_commute c x

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

#push-options "--fuel 4 --ifuel 1"
let intro_exists_erased_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_IntroExistsErased? d})
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =
  let t0 = t in
  let T_IntroExistsErased _ u t p e t_typing p_typing e_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let rp = elab_term p in
  let re = elab_term e in
  let rt_typing : RT.typing _ rt (R.pack_ln (R.Tv_Type ru)) =
      tot_typing_soundness t_typing in

  let rp_typing
      : RT.typing _
                  (mk_exists ru rt (mk_abs rt R.Q_Explicit rp)) vprop_tm =
      tot_typing_soundness p_typing
  in
  let rp_typing
      : RT.typing _
                  (mk_abs rt R.Q_Explicit rp)
                  (mk_arrow (rt, R.Q_Explicit) vprop_tm) =
        Exists.exists_inversion rp_typing
  in
  let re_typing : RT.typing _ re _ =
      tot_typing_soundness e_typing
  in
  let reveal_re = elab_term (mk_reveal u t e) in

  // reveal_re is ln
  LN.tot_typing_ln e_typing;
  elab_ln (mk_reveal u t e) (-1);

  //rp is (ln' 0)
  LN.tot_typing_ln p_typing;
  elab_ln p 0;
  
  RT.beta_reduction rt R.Q_Explicit rp reveal_re;    

  Exists.intro_exists_erased_soundness rt_typing rp_typing re_typing

let intro_exists_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_IntroExists? d })
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
        Exists.exists_inversion rp_typing
  in
  let re_typing : RT.typing _ re _ =
      tot_typing_soundness e_typing
  in

  // re is ln
  LN.tot_typing_ln e_typing;
  elab_ln e (-1);

  //rp is (ln' 0)
  LN.tot_typing_ln p_typing;
  elab_ln p 0;

  RT.beta_reduction rt R.Q_Explicit rp re;

  Exists.intro_exists_soundness rt_typing rp_typing re_typing
#pop-options

#push-options "--z3rlimit_factor 8 --fuel 4 --ifuel 2"
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

  // rt is ln
  LN.tot_typing_ln t_typing;
  elab_ln t (-1);

  //rp is (ln' 0)
  LN.tot_typing_ln p_typing;
  elab_ln p 0;

  calc (==) {
    elab_term (close_term' (open_term' p (mk_reveal u t x_tm) 0) x 0);
       (==) {
               RT.beta_reduction rt R.Q_Explicit rp (Pulse.Reflection.Util.mk_reveal ru rt rx_tm)
            }
    Exists.elim_exists_post_body ru rt (mk_abs rt R.Q_Explicit rp) x;
  };
  Exists.elim_exists_soundness x rt_typing rp_typing
#pop-options

#push-options "--z3rlimit_factor 4 --fuel 4 --ifuel 2"
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

  // (elab_term inv) is (ln 0)
  LN.tot_typing_ln inv_typing;
  elab_ln inv 0;

  elab_open_commute' inv tm_true 0;
  RT.beta_reduction bool_tm R.Q_Explicit (elab_term inv) true_tm;

  let rbody_typing
    : RT.typing _ (elab_st_typing body_typing)
        (mk_stt_comp uzero unit_tm
           (R.pack_ln (R.Tv_App rinv (true_tm, R.Q_Explicit)))
           (mk_abs unit_tm R.Q_Explicit (mk_exists uzero bool_tm rinv))) =
    soundness f g body (comp_while_body inv) body_typing in

  elab_open_commute' inv tm_false 0;
  RT.beta_reduction bool_tm R.Q_Explicit (elab_term inv) false_tm;

  While.while_soundness rinv_typing rcond_typing rbody_typing
#pop-options

#push-options "--z3rlimit_factor 4 --fuel 4 --ifuel 2"
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

let stc_soundness
  (#f:stt_env)
  (#g:env)
  (#st:st_comp)
  (d_st:st_comp_typing f g st)
  
  : GTot (RT.typing (extend_env_l f g)
                    (elab_term st.res)
                    (RT.tm_type (elab_universe st.u)) &
          RT.typing (extend_env_l f g)
                    (elab_term st.pre)
                    vprop_tm &
          RT.typing (extend_env_l f g)
                    (mk_abs (elab_term st.res) R.Q_Explicit
                                                   (elab_term st.post))
                    (post1_type_bind (elab_term st.res))) =
   
  let STC _ st x dres dpre dpost = d_st in
  let res_typing = tot_typing_soundness dres in
  let pre_typing = tot_typing_soundness dpre in      
  calc (==) {
    RT.close_term (elab_term (open_term st.post x)) x;
       (==) { elab_open_commute st.post x }
    RT.close_term (RT.open_term (elab_term st.post) x) x;
       (==) { 
              elab_freevars st.post;
              RT.close_open_inverse (elab_term st.post) x
            }
    elab_term st.post;
  };
  let post_typing  = mk_t_abs_tot f g RT.pp_name_default dres dpost in
  res_typing, pre_typing, post_typing

#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 2"
let comp_typing_soundness (f:stt_env)
                          (g:env)
                          (c:comp)
                          (uc:universe)
                          (d:comp_typing f g c uc)
  : GTot (RT.typing (extend_env_l f g) (elab_comp c) (RT.tm_type (elab_universe uc)))
         (decreases d)
  = match d with
    | CT_Tot _ t _ dt ->
      tot_typing_soundness dt
      
    | CT_ST _ st d_st -> 
      let res_typing, pre_typing, post_typing = stc_soundness d_st in
      STT.stt_typing res_typing pre_typing post_typing

    | CT_STAtomic _ i st d_i d_st -> 
      let i_typing = tot_typing_soundness d_i in
      let res_typing, pre_typing, post_typing = stc_soundness d_st in
      STT.stt_atomic_typing res_typing i_typing pre_typing post_typing

    | CT_STGhost _ i st d_i d_st -> 
      let i_typing = tot_typing_soundness d_i in
      let res_typing, pre_typing, post_typing = stc_soundness d_st in
      STT.stt_ghost_typing res_typing i_typing pre_typing post_typing
#pop-options

let admit_soundess
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_Admit? d})
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_Admit _ s c st_typing = d in

  let rt_typing, rpre_typing, rpost_typing = stc_soundness st_typing in
  match c with
  | STT ->
    Admit.stt_admit_soundness rt_typing rpre_typing rpost_typing
  | STT_Atomic ->
    Admit.stt_atomic_admit_soundness rt_typing rpre_typing rpost_typing
  | STT_Ghost ->
    Admit.stt_ghost_admit_soundness rt_typing rpre_typing rpost_typing

#push-options "--z3rlimit_factor 10 --fuel 4 --ifuel 2"
let return_soundess
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_Return? d})
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_Return _ ctag use_eq u t e post x t_typing e_typing post_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let re = elab_term e in
  let rpost = elab_term post in
  let rpost = mk_abs rt R.Q_Explicit rpost in
  let rt_typing : RT.typing _ rt (R.pack_ln (R.Tv_Type ru)) =
    tot_typing_soundness t_typing in
  let re_typing : RT.typing _ re rt =
    tot_typing_soundness e_typing in
  let rpost_typing
    : RT.typing _ rpost
                  (mk_arrow (rt, R.Q_Explicit) vprop_tm) =
    mk_t_abs_tot f g RT.pp_name_default t_typing post_typing in

  // re is ln
  LN.tot_typing_ln e_typing;
  elab_ln e (-1);

  // (elab_term post) is (ln 0)
  RT.well_typed_terms_are_ln _ rpost _ rpost_typing;
  assert (RT.ln' (elab_term post) 0);

  elab_open_commute' post e 0;
  RT.beta_reduction rt R.Q_Explicit (elab_term post) re;
  
  match ctag, use_eq with
  | STT, true ->
    Return.return_stt_typing x rt_typing re_typing rpost_typing
  | STT, false -> 
    Return.return_stt_noeq_typing rt_typing re_typing rpost_typing
  | STT_Atomic, true ->
    Return.return_stt_atomic_typing x rt_typing re_typing rpost_typing
  | STT_Atomic, false -> 
    Return.return_stt_atomic_noeq_typing rt_typing re_typing rpost_typing
  | STT_Ghost, true ->
    Return.return_stt_ghost_typing x rt_typing re_typing rpost_typing
  | STT_Ghost, false -> 
    Return.return_stt_ghost_noeq_typing rt_typing re_typing rpost_typing
#pop-options

#push-options "--z3rlimit_factor 10 --fuel 8 --ifuel 1"
let par_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_Par? d})
  (soundness: soundness_t d)
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_Par _ eL cL eR cR x cL_typing cR_typing eL_typing eR_typing = d in

  let ru = elab_universe (comp_u cL) in
  let raL = elab_term (comp_res cL) in
  let raR = elab_term (comp_res cR) in
  let rpreL = elab_term (comp_pre cL) in
  let rpostL = mk_abs raL R.Q_Explicit (elab_term (comp_post cL)) in
  let rpreR = elab_term (comp_pre cR) in
  let rpostR = mk_abs raR R.Q_Explicit (elab_term (comp_post cR)) in
  let reL = elab_st_typing eL_typing in
  let reR = elab_st_typing eR_typing in

  let reL_typing
    : RT.typing _ reL (elab_comp cL) =
    soundness f g eL cL eL_typing in

  let reR_typing
    : RT.typing _ reR (elab_comp cR) =
    soundness f g eR cR eR_typing in

  let (raL_typing, rpreL_typing, rpostL_typing)
    : (RT.typing _ raL (R.pack_ln (R.Tv_Type ru)) &
       RT.typing _ rpreL vprop_tm &
       RT.typing _ rpostL (mk_arrow (raL, R.Q_Explicit) vprop_tm)) =

    inversion_of_stt_typing f g cL ru (comp_typing_soundness f g cL (comp_u cL) cL_typing) in

  let (raR_typing, rpreR_typing, rpostR_typing)
    : (RT.typing _ raR (R.pack_ln (R.Tv_Type ru)) &
       RT.typing _ rpreR vprop_tm &
       RT.typing _ rpostR (mk_arrow (raR, R.Q_Explicit) vprop_tm)) =

    inversion_of_stt_typing f g cR ru (comp_typing_soundness f g cR (comp_u cR) cR_typing) in

  /////
  let uL = comp_u cL in
  let uR = comp_u cR in
  let aL = comp_res cL in
  let aR = comp_res cR in
  let postL = comp_post cL in
  let postR = comp_post cR in
  let x_tm = term_of_var x in

  // ln proofs for invoking the RT beta reduction
  RT.well_typed_terms_are_ln _ _ _ raL_typing;
  RT.well_typed_terms_are_ln _ _ _ raR_typing;
  RT.well_typed_terms_are_ln _ _ _ rpostL_typing;
  RT.well_typed_terms_are_ln _ _ _ rpostR_typing;

  calc (==) {
    elab_term (par_post uL uR aL aR postL postR x);
       (==) { }
    RT.open_or_close_term'
      (mk_star
         (RT.open_or_close_term'
            (elab_term postL)
            (RT.OpenWith (elab_term (mk_fst uL uR aL aR x_tm))) 0)
         (RT.open_or_close_term'
            (elab_term postR)
            (RT.OpenWith (elab_term (mk_snd uL uR aL aR x_tm))) 0))
      (RT.CloseVar x)
      0;
       (==) { RT.beta_reduction raL R.Q_Explicit
                (elab_term postL)
                (Pulse.Reflection.Util.mk_fst ru ru raL raR (RT.var_as_term x));
              RT.beta_reduction raR R.Q_Explicit
                (elab_term postR)
                (Pulse.Reflection.Util.mk_snd ru ru raL raR (RT.var_as_term x)) }
    Par.par_post ru raL raR rpostL rpostR x;
  };
  /////

  Par.par_soundness x raL_typing raR_typing rpreL_typing rpostL_typing
    rpreR_typing rpostR_typing
    reL_typing reR_typing
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

    // | T_Tot _ _ _ d -> tot_typing_soundness d

    | T_Abs _ x q ty u body c t_typing body_typing ->
      mk_t_abs q RT.pp_name_default t_typing body_typing    

    | T_STApp _ _ _ _ _ _ _ _ ->
      stapp_soundness _ _ _ _ d soundness

    | T_Bind _ _e1 _e2 _c1 _c2 _x _c _e1_typing _t_typing _e2_typing _bc ->
      bind_soundness d soundness mk_t_abs

    | T_Equiv _ _ _ _ _ _ ->
      stequiv_soundness _ _ _ _ d soundness

    | T_Return _ _ _ _ _ _ _ _ _ _ _ ->
      return_soundess d

    | T_If _ _ _ _ _ _ _ _ _ _ _->
      let ct_soundness f g c uc (d':_ {d' << d}) =
        comp_typing_soundness f g c uc d'
      in
      if_soundness _ _ _ _ d soundness ct_soundness

    | T_ElimExists _ _ _ _ _ _ _ ->
      elim_exists_soundness d

    | T_IntroExists _ _ _ _ _ _ _ _ ->
      intro_exists_soundness d

    | T_IntroExistsErased _ _ _ _ _ _ _ _ ->
      intro_exists_erased_soundness d

    | T_While _ _ _ _ _ _ _ ->
      while_soundness d soundness

    | T_Par _ _ _ _ _ _ _ _ _ _ ->
      par_soundness d soundness

    | T_Admit _ _ _ _ -> admit_soundess d
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
