module Pulse.Elaborate.Core
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing

open Pulse.Reflection.Util

let elab_frame (c:comp_st) (frame:term) (e:R.term) =
  let u = elab_universe (comp_u c) in
  let ty = elab_term (comp_res c) in
  let pre = elab_term (comp_pre c) in
  let post = elab_term (comp_post c) in
  if C_ST? c
  then mk_frame_stt u ty pre (mk_abs ty R.Q_Explicit post) (elab_term frame) e
  else let opened = elab_term (comp_inames c) in      
       if C_STAtomic? c
       then mk_frame_stt_atomic u ty opened pre (mk_abs ty R.Q_Explicit post) (elab_term frame) e
       else let _ = assert (C_STGhost? c) in
            mk_frame_stt_ghost u ty opened pre (mk_abs ty R.Q_Explicit post) (elab_term frame) e

let elab_sub (c1 c2:comp_st) (e:R.term) =
  let ty = elab_term (comp_res c1) in
  let u = elab_universe (comp_u c1) in
  let pre1 = elab_term (comp_pre c1) in
  let pre2 = elab_term (comp_pre c2) in
  let post1 = mk_abs ty R.Q_Explicit (elab_term (comp_post c1)) in
  let post2 = mk_abs ty R.Q_Explicit (elab_term (comp_post c2)) in
  if C_ST? c1
  then mk_sub_stt u ty pre1 pre2 post1 post2 e
  else let opened = elab_term (comp_inames c1) in
       if C_STAtomic? c1
       then mk_sub_stt_atomic u ty opened pre1 pre2 post1 post2 e
       else let _ = assert (C_STGhost? c1) in
            mk_sub_stt_ghost u ty opened pre1 pre2 post1 post2 e


let elab_bind #f #g #x #c1 #c2 #c
              (bc:bind_comp f g x c1 c2 c)
              (e1 e2:R.term)
  : R.term
  = let t1 = elab_term (comp_res c1) in
    let t2 = elab_term (comp_res c2) in
    match bc with
    | Bind_comp _ _ _ _ _ _ _ ->
      if C_ST? c1
      then
        mk_bind_stt
          (elab_universe (comp_u c1))
          (elab_universe (comp_u c2))
          t1 t2
          (elab_term (comp_pre c1))
          (mk_abs t1 R.Q_Explicit (elab_term (comp_post c1)))
          (mk_abs t2 R.Q_Explicit (elab_term (comp_post c2)))
          e1 e2
      else 
        mk_bind_ghost
          (elab_universe (comp_u c1))
          (elab_universe (comp_u c2))
          t1 t2
          (elab_term (comp_inames c1))
          (elab_term (comp_pre c1))
          (mk_abs t1 R.Q_Explicit (elab_term (comp_post c1)))
          (mk_abs t2 R.Q_Explicit (elab_term (comp_post c2)))
          e1 e2
  
    | Bind_comp_ghost_l _ _ _ _ (| reveal_a, reveal_a_typing |) _ _ _ ->
      mk_bind_ghost_atomic
        (elab_universe (comp_u c1))
        (elab_universe (comp_u c2))
        t1 t2
        (elab_term (comp_inames c1))
        (elab_term (comp_pre c1))
        (mk_abs t1 R.Q_Explicit (elab_term (comp_post c1)))
        (mk_abs t2 R.Q_Explicit (elab_term (comp_post c2)))
        e1 e2
        (elab_term reveal_a)

    | Bind_comp_ghost_r _ _ _ _ (| reveal_b, reveal_b_typing |) _ _ _ ->
      mk_bind_atomic_ghost
        (elab_universe (comp_u c1))
        (elab_universe (comp_u c2))
        t1 t2
        (elab_term (comp_inames c1))
        (elab_term (comp_pre c1))
        (mk_abs t1 R.Q_Explicit (elab_term (comp_post c1)))
        (mk_abs t2 R.Q_Explicit (elab_term (comp_post c2)))
        e1 e2
        (elab_term reveal_b)

let elab_lift #f #g #c1 #c2 (d:lift_comp f g c1 c2) (e:R.term)
  : Tot R.term
  = match d with
    | Lift_STAtomic_ST _ _ ->
      let t = elab_term (comp_res c1) in
      mk_lift_atomic_stt
        (elab_universe (comp_u c1))
        (elab_term (comp_res c1))
        t
        (mk_abs t R.Q_Explicit (elab_term (comp_post c1)))
        e
        
    | Lift_STGhost_STAtomic _ _ (| reveal_a, reveal_a_typing |) ->
      let t = elab_term (comp_res c1) in
      mk_lift_ghost_atomic
        (elab_universe (comp_u c1))
        t
        (elab_term (comp_inames c1))
        (elab_term (comp_pre c1))
        (mk_abs t R.Q_Explicit (elab_term (comp_post c1)))
        e
        (elab_term reveal_a)

let rec elab_st_typing (#f:RT.fstar_top_env)
                       (#g:env)
                       (#t:st_term)
                       (#c:comp)
                       (d:st_typing f g t c)
  : Tot R.term (decreases d)
  = match d with
    // | T_Tot _ t _ _ -> elab_term t

    | T_Abs _ x qual ty_pulse _u body _c ty_typing body_typing ->
      let ty = elab_term ty_pulse in
      let body = elab_st_typing body_typing in
      let ppname = (as_binder ty_pulse).binder_ppname in
      mk_abs_with_name ppname ty (elab_qual qual) (RT.close_term body x) //this closure should be provably redundant by strengthening the conditions on x

    | T_STApp _ head  _formal qual _res arg head_typing arg_typing ->
      let head = elab_term head in
      let arg = elab_term arg in
      R.mk_app head [(arg, elab_qual qual)]

    | T_Return _ c use_eq u ty t post _ _ _ _ ->
      let ru = elab_universe u in
      let rty = elab_term ty in
      let rt = elab_term t in
      let rp = elab_term post in
      let rp = mk_abs rty R.Q_Explicit rp in
      (match c, use_eq with
       | STT, true -> mk_stt_return ru rty rt rp
       | STT, false -> mk_stt_return_noeq ru rty rt rp
       | STT_Atomic, true -> mk_stt_atomic_return ru rty rt rp
       | STT_Atomic, false -> mk_stt_atomic_return_noeq ru rty rt rp
       | STT_Ghost, true -> mk_stt_ghost_return ru rty rt rp
       | STT_Ghost, false -> mk_stt_ghost_return_noeq ru rty rt rp)

    | T_Bind _ e1 e2 c1 c2 x c e1_typing t_typing e2_typing bc ->
      let e1 = elab_st_typing e1_typing in
      let e2 = elab_st_typing e2_typing in
      let ty1 = elab_term (comp_res c1) in
      elab_bind bc e1 (mk_abs ty1 R.Q_Explicit (RT.close_term e2 x))
      
    | T_Frame _ _ c frame _frame_typing e_typing ->
      let e = elab_st_typing e_typing in
      elab_frame c frame e
      
    | T_Equiv _ _ c1 c2 e_typing _ ->
      let e = elab_st_typing e_typing in
      elab_sub c1 c2 e

    | T_Lift _ _ c1 c2 e_typing lc ->
      let e = elab_st_typing e_typing in
      elab_lift lc e

    | T_If _ b _ _ _ _ _ _ e1_typing e2_typing _c_typing ->
      let rb = elab_term b in
      let re1 = elab_st_typing e1_typing in
      let re2 = elab_st_typing e2_typing in
      RT.mk_if rb re1 re2

    | T_ElimExists _ u t p _ d_t d_exists ->
      let ru = elab_universe u in
      let rt = elab_term t in
      let rp = elab_term p in
      mk_elim_exists ru rt (mk_abs rt R.Q_Explicit rp)

    | T_IntroExists _ u t p e _ _ _ ->
      let ru = elab_universe u in
      let rt = elab_term t in
      let rp = elab_term p in
      let re = elab_term e in
      mk_intro_exists ru rt (mk_abs rt R.Q_Explicit rp) re

    | T_IntroExistsErased _ u t p e _ _ _ ->
      let ru = elab_universe u in
      let rt = elab_term t in
      let rp = elab_term p in
      let re = elab_term e in
      mk_intro_exists_erased ru rt (mk_abs rt R.Q_Explicit rp) re

    | T_While _ inv _ _ _ cond_typing body_typing ->
      let inv = elab_term inv in
      let cond = elab_st_typing cond_typing in
      let body = elab_st_typing body_typing in
      mk_while (mk_abs bool_tm R.Q_Explicit inv) cond body

    | T_Par _ eL cL eR cR _ _ _ eL_typing eR_typing ->
      let ru = elab_universe (comp_u cL) in
      let raL = elab_term (comp_res cL) in
      let raR = elab_term (comp_res cR) in
      let rpreL = elab_term (comp_pre cL) in
      let rpostL = elab_term (comp_post cL) in
      let rpreR = elab_term (comp_pre cR) in
      let rpostR = elab_term (comp_post cR) in
      let reL = elab_st_typing eL_typing in
      let reR = elab_st_typing eR_typing in
      mk_par ru
        raL
        raR
        rpreL
        (mk_abs raL R.Q_Explicit rpostL)
        rpreR
        (mk_abs raR R.Q_Explicit rpostR)
        reL reR

				| T_Rewrite _ p q _ _ ->
				  let rp = elab_term p in
						let rq = elab_term q in
						mk_rewrite rp rq

    | T_Admit _ {u;res;pre;post} c _ ->
      let ru = elab_universe u in
      let rres = elab_term res in
      let rpre = elab_term pre in
      let rpost = elab_term post in
      let rpost = mk_abs rres R.Q_Explicit rpost in
      (match c with
       | STT -> mk_stt_admit ru rres rpre rpost
       | STT_Atomic -> mk_stt_atomic_admit ru rres rpre rpost
       | STT_Ghost -> mk_stt_ghost_admit ru rres rpre rpost)
