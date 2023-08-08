module Pulse.Soundness
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
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
module WithLocal = Pulse.Soundness.WithLocal
module Rewrite = Pulse.Soundness.Rewrite
module Comp = Pulse.Soundness.Comp
module LN = Pulse.Typing.LN
module FV = Pulse.Typing.FV
module STT = Pulse.Soundness.STT

module Typing = Pulse.Typing
module EPure = Pulse.Elaborate.Pure
module WT= Pulse.Steel.Wrapper.Typing

let tabs_t (d:'a) = 
    #g:stt_env ->
    #u:universe ->
    #ty:term ->
    q:option qualifier ->
    ppname:ppname ->
    t_typing:tot_typing g ty (tm_type u) { t_typing << d } ->
    #body:st_term ->
    #x:var { None? (lookup g x) /\ ~(x `Set.mem` freevars_st body) } ->
    #c:comp ->
    body_typing:st_typing (push_binding g x ppname ty) (open_st_term body x) c { body_typing << d } ->
    GTot (RT.tot_typing (elab_env g)
            (mk_abs_with_name ppname.name (elab_term ty) (elab_qual q) (RT.close_term (elab_st_typing body_typing) x))
            (elab_term (tm_arrow {binder_ty=ty;binder_ppname=ppname} q (close_comp c x))))

let lift_soundness
  (g:stt_env)
  (t:st_term)
  (c:comp)
  (d:st_typing g t c{T_Lift? d})
  (soundness:soundness_t d)
  : GTot (RT.tot_typing (elab_env g) (elab_st_typing d) (elab_comp c)) =
  LN.st_typing_ln d;
  let T_Lift _ e c1 c2 e_typing lc = d in
  LN.st_typing_ln e_typing;
  match lc with
  | Lift_STAtomic_ST _ _ ->
    Lift.elab_lift_stt_atomic_typing g
      c1 c2 _ (soundness _ _ _ e_typing) lc
  | Lift_STGhost_STAtomic _ _ w ->
    let (| reveal_a, reveal_a_typing |) = w in
    Lift.elab_lift_stt_ghost_typing g
      c1 c2 _ (soundness _ _ _ e_typing) lc
      _ (tot_typing_soundness reveal_a_typing)

let frame_soundness
  (g:stt_env)
  (t:st_term)
  (c:comp)
  (d:st_typing g t c{T_Frame? d})
  (soundness:soundness_t d)
  : GTot (RT.tot_typing (elab_env g) (elab_st_typing d) (elab_comp c)) =

  let T_Frame _ e c frame frame_typing e_typing = d in
  let r_e_typing = soundness _ _ _ e_typing in
  LN.st_typing_ln e_typing;
  Frame.elab_frame_typing g _ _ frame frame_typing r_e_typing

let stapp_soundness
  (g:stt_env)
  (t:st_term)
  (c:comp)
  (d:st_typing g t c{T_STApp? d})
  (soundness:soundness_t d)
  : GTot (RT.tot_typing (elab_env g) (elab_st_typing d) (elab_comp c)) =

  let T_STApp _ head formal q res arg head_typing arg_typing = d in
  let r_head = elab_term head in
  let r_arg = elab_term arg in
  let r_head_typing
    : RT.tot_typing _ r_head
        (elab_term (tm_arrow {binder_ty=formal;binder_ppname=ppname_default} q res))
    = tot_typing_soundness head_typing
  in
  let r_arg_typing = tot_typing_soundness arg_typing in
  RT.T_App _ _ _ (binder_of_t_q_s (elab_term formal) (elab_qual q) RT.pp_name_default)
                 (elab_comp res)
                 _
                 r_head_typing
                 r_arg_typing

let stghostapp_soundness
  (g:stt_env)
  (t:st_term)
  (c:comp)
  (d:st_typing g t c{T_STGhostApp? d})
  (soundness:soundness_t d)
  : GTot (RT.tot_typing (elab_env g) (elab_st_typing d) (elab_comp c)) =

  let T_STGhostApp _ head formal q res arg x head_typing d_non_info arg_typing = d in
  let r_head = elab_term head in
  let r_arg = elab_term arg in
  let r_binder = {binder_ty=formal;binder_ppname=ppname_default} in
  let head_t = tm_arrow r_binder q res in
  let r_head_t = mk_arrow_with_name ppname_default.name (elab_term formal, elab_qual q)
                                                        (elab_comp res) in
  let r_head_typing : RT.tot_typing _ r_head r_head_t
    = tot_typing_soundness head_typing in
  let r_arg_typing = ghost_typing_soundness arg_typing in
  
  assume (elab_env (push_binding g x ppname_default formal) ==
          RT.extend_env (elab_env g) x (elab_term formal));
  assume ((T.E_Total, elab_comp (open_comp_with res (null_var x))) ==
          RT.open_comp_typ (T.E_Total, elab_comp res) x);
  assume ((T.E_Ghost, elab_comp (open_comp_with res (null_var x))) ==
          RT.open_comp_typ (T.E_Ghost, elab_comp res) x);
  let d_rel_comp
    : RT.related_comp (elab_env (push_binding g x ppname_default formal))
                      (T.E_Total, elab_comp (open_comp_with res (null_var x)))
                      RT.R_Sub
                      (T.E_Ghost, elab_comp (open_comp_with res (null_var x))) =
    RT.Relc_total_ghost _ _ in

  let r_head_t_ghost = mk_ghost_arrow_with_name ppname_default.name (elab_term formal, elab_qual q)
                                                                    (elab_comp res) in


  assert (r_head_t == RT.mk_arrow_ct (elab_term formal) (elab_qual q) (T.E_Total, elab_comp res));
  assert (r_head_t_ghost == RT.mk_arrow_ct (elab_term formal) (elab_qual q) (T.E_Ghost, elab_comp res));

  assume (None? (RT.lookup_bvar (elab_env g) x) /\
          ~ (x `Set.mem` ((RT.freevars_comp_typ (T.E_Total, elab_comp res)) `Set.union`
                          (RT.freevars_comp_typ (T.E_Ghost, elab_comp res)))));
  let d_rel_t_arrow
    : RT.related (elab_env g)
                 r_head_t
                 RT.R_Sub
                 r_head_t_ghost
    = RT.Rel_arrow _ (elab_term formal) (elab_term formal) (elab_qual q) (T.E_Total, elab_comp res) (T.E_Ghost, elab_comp res)
        RT.R_Sub x (RT.Rel_equiv _ _ _ _ (RT.EQ_Refl _ _))
        d_rel_comp in

  let r_head_typing : RT.tot_typing _ r_head r_head_t_ghost =
    RT.T_Sub _ _ _ _ r_head_typing (RT.Relc_typ _ _ _ T.E_Total _ d_rel_t_arrow) in

  let r_head_typing : RT.ghost_typing _ r_head r_head_t_ghost =
    RT.T_Sub _ _ _ _ r_head_typing (RT.Relc_total_ghost _ _) in

  let d : RT.typing (elab_env g) (elab_st_typing d) (T.E_Ghost, elab_comp (open_comp_with res arg)) =
    RT.T_App _ _ _ (binder_of_t_q_s (elab_term formal) (elab_qual q) RT.pp_name_default)
      (elab_comp res)
      _
      r_head_typing
      r_arg_typing in

  let d_non_info
    : RT.non_informative (elab_env (push_binding g x ppname_default formal))
                         (elab_comp (open_comp_with res (null_var x))) = d_non_info in

  // TODO: substitution lemma in RT for non_informative judgment
  let d_non_info
    : RT.non_informative (elab_env g) (elab_comp (open_comp_with res arg)) = magic () in

  RT.T_Sub _ _ _ _ d (RT.Relc_ghost_total _ _ d_non_info)

let stequiv_soundness
  (g:stt_env)
  (t:st_term)
  (c:comp)
  (d:st_typing g t c{T_Equiv? d})
  (soundness:soundness_t d)            
  : GTot (RT.tot_typing (elab_env g) (elab_st_typing d) (elab_comp c)) =

  let T_Equiv _ e c c' e_typing equiv = d in
  LN.st_typing_ln d;
  LN.st_typing_ln e_typing;
  let r_e_typing = soundness _ _ _ e_typing in 
  STEquiv.st_equiv_soundness _ _ _ equiv _ r_e_typing


#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 30"

let bind_soundness
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c{T_Bind? d})
  (soundness: soundness_t d)
  (mk_t_abs: tabs_t d)
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c))
  = let T_Bind _ e1 e2 c1 c2 _ x c e1_typing t_typing e2_typing bc = d in
    LN.st_typing_ln e1_typing;
    LN.st_typing_ln e2_typing;      
    FV.st_typing_freevars_inv e1_typing x;
    let r1_typing
      : RT.tot_typing _ _ (elab_comp c1)
      = soundness _ _ _ e1_typing
    in
    let r2_typing
      : RT.tot_typing _ _ (elab_term (tm_arrow (null_binder (comp_res c1)) None (close_comp c2 x)))
      = mk_t_abs None _ t_typing e2_typing
    in
    match bc with
    | Bind_comp _ _ _ _ t2_typing y post2_typing ->
         Bind.elab_bind_typing g _ _ _ x _ r1_typing _ r2_typing bc 
                               (tot_typing_soundness t2_typing)
                               (mk_t_abs_tot _ ppname_default t2_typing post2_typing)
                               
    | Bind_comp_ghost_l _ _ _ _ (| reveal_a, reveal_a_typing |) t2_typing y post2_typing ->
         Bind.elab_bind_ghost_l_typing g _ _ _ x _ r1_typing
           _ r2_typing bc
           (tot_typing_soundness t2_typing)
           (mk_t_abs_tot _ ppname_default t2_typing post2_typing)
           (elab_term reveal_a)
           (tot_typing_soundness reveal_a_typing)
    | Bind_comp_ghost_r _ _ _ _ (| reveal_b, reveal_b_typing |) t2_typing y post2_typing ->
         Bind.elab_bind_ghost_r_typing g _ _ _ x _ r1_typing
           _ r2_typing bc
           (tot_typing_soundness t2_typing)
           (mk_t_abs_tot _ ppname_default t2_typing post2_typing)
           (elab_term reveal_b)
           (tot_typing_soundness reveal_b_typing)
#pop-options

#push-options "--z3rlimit_factor 4 --fuel 4 --ifuel 2"
let if_soundness
  (g:stt_env)
  (t:st_term)
  (c:comp)
  (d:st_typing g t c{T_If? d})
  (soundness:soundness_t d)
  (ct_soundness: (g:stt_env -> c:comp -> uc:universe ->
                  d':comp_typing g c uc{d' << d} ->
              GTot (RT.tot_typing (elab_env g)
                              (elab_comp c)
                              (RT.tm_type uc))))
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c)) =

  let T_If _ b e1 e2  _ u_c hyp b_typing e1_typing e2_typing (E c_typing) = d in
  let rb_typing : RT.tot_typing (elab_env g)
                                (elab_term b)
                                RT.bool_ty =
    tot_typing_soundness b_typing in
  let g_then = push_binding g hyp ppname_default (mk_eq2 u0 tm_bool b tm_true) in
  elab_push_binding g hyp (mk_eq2 u0 tm_bool b tm_true);
  let re1_typing

    : RT.tot_typing (RT.extend_env (elab_env g)
                               hyp
                               (RT.eq2 (R.pack_universe R.Uv_Zero)
                                       RT.bool_ty
                                       (elab_term b)
                                       RT.true_bool))
                (elab_st_typing e1_typing)
                (elab_comp c) =
    soundness g_then e1 c e1_typing in
  let g_else = push_binding g hyp ppname_default (mk_eq2 u0 tm_bool b tm_false) in
  elab_push_binding g hyp (mk_eq2 u0 tm_bool b tm_false);
  let re2_typing
    : RT.tot_typing (RT.extend_env (elab_env g)
                               hyp
                               (RT.eq2 (R.pack_universe R.Uv_Zero)
                                       RT.bool_ty
                                       (elab_term b)
                                       RT.false_bool))
                (elab_st_typing e2_typing)
                (elab_comp c) =
    soundness g_else e2 c e2_typing in
  let c_typing = 
    ct_soundness _ _ _ c_typing
  in
  assume (~(hyp `Set.mem` RT.freevars (elab_st_typing e1_typing)));
  assume (~(hyp `Set.mem` RT.freevars (elab_st_typing e2_typing)));  
  RT.T_If _ _ _ _ _ _ _ _ _ rb_typing re1_typing re2_typing c_typing
#pop-options

#push-options "--query_stats --fuel 2 --ifuel 2"
let rec soundness (g:stt_env)
                  (t:st_term)
                  (c:comp)
                  (d:st_typing g t c)
  : GTot (RT.tot_typing (elab_env g) (elab_st_typing d) (elab_comp c))
         (decreases d)
  = let mk_t_abs (#g:stt_env)
                 (#u:universe)
                 (#ty:term)
                 (q:option qualifier)
                 (ppname:ppname)
                 (t_typing:tot_typing g ty (tm_type u) { t_typing << d })
                 (#body:st_term)
                 (#x:var { None? (lookup g x) /\ ~(x `Set.mem` freevars_st body) })
                 (#c:comp)
                 (body_typing:st_typing (push_binding g x ppname ty) (open_st_term body x) c { body_typing << d })
      : GTot (RT.tot_typing (elab_env g)
                (mk_abs_with_name ppname.name (elab_term ty) (elab_qual q) (RT.close_term (elab_st_typing body_typing) x))
                (elab_term (tm_arrow {binder_ty=ty;binder_ppname=ppname} q (close_comp c x))))
      = let r_t_typing = tot_typing_soundness t_typing in
        let r_body_typing = soundness _ _ _ body_typing in
        mk_t_abs g #_ #_ #_ #t_typing ppname r_t_typing r_body_typing
    in
    LN.st_typing_ln d;
    match d with
    | T_Lift _ _ _ _ _ _ ->
      lift_soundness _ _ _ d soundness
    | T_Frame _ _ _ _ _ _ ->
      frame_soundness _ _ _ d soundness

    | T_Abs _ x q ty u body c t_typing body_typing ->
      mk_t_abs q ppname_default t_typing body_typing    

    | T_STApp _ _ _ _ _ _ _ _ ->
      stapp_soundness _ _ _ d soundness

    | T_Bind _ _e1 _e2 _c1 _c2 _b _x _c _e1_typing _t_typing _e2_typing _bc ->
      bind_soundness d soundness mk_t_abs

    | T_TotBind _ _ _ _ _ _ _ _ ->
      Bind.tot_bind_typing d soundness

    | T_GhostBind _ _ _ _ _ _ _ _ _ ->
      Bind.ghost_bind_typing d soundness

    | T_Equiv _ _ _ _ _ _ ->
      stequiv_soundness _ _ _ d soundness

    | T_Return _ _ _ _ _ _ _ _ _ _ _ ->
      Return.return_soundess d

    | T_If _ _ _ _ _ _ _ _ _ _ _->
      let ct_soundness g c uc (d':_ {d' << d}) =
        Comp.comp_typing_soundness g c uc d'
      in
      if_soundness _ _ _ d soundness ct_soundness

    | T_Match _ _ _ _ _ _ _ _ _ _->
      let ct_soundness g c uc (d':_ {d' << d}) =
        Comp.comp_typing_soundness g c uc d'
      in
      Pulse.Soundness.Match.match_soundness _ _ _ d soundness ct_soundness

    | T_IntroPure _ _ _ _  ->
      admit()
      
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

    | T_WithLocal _ _ _ _ _ _ _ _ _ _ ->
      WithLocal.withlocal_soundness d soundness

    | T_Rewrite _ _ _ _ _ ->
      Rewrite.rewrite_soundness d

    | T_Admit _ _ _ _ -> Admit.admit_soundess d
#pop-options

let soundness_lemma
  (g:stt_env)
  (t:st_term)
  (c:comp)
  (d:st_typing g t c)
  : Lemma (ensures RT.tot_typing (elab_env g)
                                 (elab_st_typing d)
                                 (elab_comp c))
  = FStar.Squash.bind_squash
      #(st_typing g t c)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness g t c d))
