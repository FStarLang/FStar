module Pulse.Soundness
module RT = FStar.Reflection.Typing
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
module Rewrite = Pulse.Soundness.Rewrite
module Comp = Pulse.Soundness.Comp
module LN = Pulse.Typing.LN
module FV = Pulse.Typing.FV
module STT = Pulse.Soundness.STT

module Typing = Pulse.Typing
module EPure = Pulse.Elaborate.Pure
module WT= Pulse.Steel.Wrapper.Typing

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
      Return.return_soundess d

    | T_If _ _ _ _ _ _ _ _ _ _ _->
      let ct_soundness f g c uc (d':_ {d' << d}) =
        Comp.comp_typing_soundness f g c uc d'
      in
      if_soundness _ _ _ _ d soundness ct_soundness

    | T_ElimExists _ _ _ _ _ _ _ ->
      Exists.elim_exists_soundness d

    | T_IntroExists _ _ _ _ _ _ _ _ ->
      Exists.intro_exists_soundness d

    | T_IntroExistsErased _ _ _ _ _ _ _ _ ->
      Exists.intro_exists_erased_soundness d

    | T_While _ _ _ _ _ _ _ ->
      While.while_soundness d soundness

    | T_Par _ _ _ _ _ _ _ _ _ _ ->
      Par.par_soundness d soundness

    | T_WithLocal _ _ _ _ _ _ _ _ _ _ -> admit ()

    | T_Rewrite _ _ _ _ _ ->
      Rewrite.rewrite_soundness d

    | T_Admit _ _ _ _ -> Admit.admit_soundess d
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
