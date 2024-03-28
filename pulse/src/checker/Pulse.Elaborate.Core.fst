(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Elaborate.Core

open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing

module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2

module S = Pulse.Syntax
module RU = Pulse.RuntimeUtils

open Pulse.Reflection.Util

let elab_frame (c:comp_st) (frame:term) (e:R.term) =
  let u = comp_u c in
  let ty = elab_term (comp_res c) in
  let pre = elab_term (comp_pre c) in
  let post = elab_term (comp_post c) in
  if C_ST? c
  then mk_frame_stt u ty pre (mk_abs ty R.Q_Explicit post) (elab_term frame) e
  else if C_STAtomic? c
  then let opened = elab_term (comp_inames c) in      
       mk_frame_stt_atomic u ty opened pre (mk_abs ty R.Q_Explicit post) (elab_term frame) e
  else mk_frame_stt_ghost u ty pre (mk_abs ty R.Q_Explicit post) (elab_term frame) e

let elab_sub (c1 c2:comp_st) (e:R.term) =
  let ty = elab_term (comp_res c1) in
  let u = comp_u c1 in
  let pre1 = elab_term (comp_pre c1) in
  let pre2 = elab_term (comp_pre c2) in
  let post1 = mk_abs ty R.Q_Explicit (elab_term (comp_post c1)) in
  let post2 = mk_abs ty R.Q_Explicit (elab_term (comp_post c2)) in
  if C_ST? c1
  then mk_sub_stt u ty pre1 pre2 post1 post2 e
  else if C_STAtomic? c1
  then let opened = elab_term (comp_inames c1) in
       mk_sub_stt_atomic u ty opened pre1 pre2 post1 post2 e
  else mk_sub_stt_ghost u ty pre1 pre2 post1 post2 e


let elab_bind #g #x #c1 #c2 #c
              (bc:bind_comp g x c1 c2 c)
              (e1 e2:R.term)
  : R.term
  = let t1 = elab_term (comp_res c1) in
    let t2 = elab_term (comp_res c2) in
    match c1 with
    | C_ST _ ->
      mk_bind_stt
          (comp_u c1)
          (comp_u c2)
          t1 t2
          (elab_term (comp_pre c1))
          (mk_abs t1 R.Q_Explicit (elab_term (comp_post c1)))
          (mk_abs t2 R.Q_Explicit (elab_term (comp_post c2)))
          e1 e2
    | C_STGhost _ ->
        mk_bind_ghost
          (comp_u c1)
          (comp_u c2)
          t1 t2
          (elab_term (comp_pre c1))
          (mk_abs t1 R.Q_Explicit (elab_term (comp_post c1)))
          (mk_abs t2 R.Q_Explicit (elab_term (comp_post c2)))
          e1 e2
    | C_STAtomic inames obs1 _ ->
      let C_STAtomic _ obs2 _ = c2 in      
      mk_bind_atomic
          (comp_u c1)
          (comp_u c2)
          (elab_observability obs1)
          (elab_observability obs2)
          (elab_term (comp_inames c1))
          t1 t2
          (elab_term (comp_pre c1))
          (mk_abs t1 R.Q_Explicit (elab_term (comp_post c1)))
          (mk_abs t2 R.Q_Explicit (elab_term (comp_post c2)))
          e1 e2
  
let elab_lift #g #c1 #c2 (d:lift_comp g c1 c2) (e:R.term)
  : Tot R.term
  = match d with
    | Lift_STAtomic_ST _ _ ->
      let t = elab_term (comp_res c1) in
      mk_lift_atomic_stt
        (comp_u c1)
        (elab_term (comp_res c1))
        t
        (mk_abs t R.Q_Explicit (elab_term (comp_post c1)))
        e

    | Lift_Observability _ c o2 ->
      let t = elab_term (comp_res c1) in
      mk_lift_observability
        (comp_u c1)
        (elab_observability (C_STAtomic?.obs c))
        (elab_observability o2)
        (elab_term (comp_inames c1))
        t
        (elab_term (comp_pre c1))
        (mk_abs t R.Q_Explicit (elab_term (comp_post c1)))
        e
            
    | Lift_Ghost_Neutral _ _ (| reveal_a, reveal_a_typing |) ->
      let t = elab_term (comp_res c1) in
      mk_lift_ghost_neutral
        (comp_u c1)
        t
        (elab_term (comp_pre c1))
        (mk_abs t R.Q_Explicit (elab_term (comp_post c1)))
        e
        (elab_term reveal_a)

    | Lift_Neutral_Ghost _ c ->
      let t = elab_term (comp_res c1) in
      mk_lift_neutral_ghost
        (comp_u c1)
        t
        (elab_term (comp_pre c1))
        (mk_abs t R.Q_Explicit (elab_term (comp_post c1)))
        e

let intro_pure_tm (p:term) =
  let open Pulse.Reflection.Util in
  wtag (Some STT_Ghost) 
       (Tm_STApp
        { head =
            tm_pureapp (tm_fvar (as_fv (mk_pulse_lib_core_lid "intro_pure")))
                       None
                       p;
          arg_qual = None;
          arg = S.wr (`()) Range.range_0 })

let simple_arr (t1 t2 : R.term) : R.term =
  let b = R.pack_binder {
           sort = t1;
           ppname = Sealed.seal "x";
           qual = R.Q_Explicit;
           attrs = [] } in
  R.pack_ln (R.Tv_Arrow b (R.pack_comp (R.C_Total t2)))

let elab_st_sub (#g:env) (#c1 #c2 : comp)
     (d_sub : st_sub g c1 c2)
   : Tot (t:R.term
          & RT.tot_typing (elab_env g) t (simple_arr (elab_comp c1) (elab_comp c2)))
= RU.magic_s "elab_st_sub"

let rec elab_st_typing (#g:env)
                       (#t:st_term)
                       (#c:comp)
                       (d:st_typing g t c)
  : Tot R.term (decreases d)
  = match d with
    // | T_Tot _ t _ _ -> elab_term t

    | T_Abs _ x qual b _u body _c ty_typing body_typing ->
      let ty = elab_term b.binder_ty in
      let ppname = b.binder_ppname.name in
      let body = elab_st_typing body_typing in
      mk_abs_with_name ppname ty (elab_qual qual) (RT.close_term body x) //this closure should be provably redundant by strengthening the conditions on x


    | T_STApp _ head _ qual _ arg _ _
    | T_STGhostApp _ head _ qual _ arg _ _ _ _ ->
      let head = elab_term head in
      let arg = elab_term arg in
      R.mk_app head [(arg, elab_qual qual)]

    | T_Return _ c use_eq u ty t post _ _ _ _ ->
      let ru = u in
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

    | T_Bind _ e1 e2 c1 c2 b x c e1_typing t_typing e2_typing bc ->
      let e1 = elab_st_typing e1_typing in
      let e2 = elab_st_typing e2_typing in
      let ty1 = elab_term (comp_res c1) in
      elab_bind bc e1 (mk_abs_with_name b.binder_ppname.name ty1 R.Q_Explicit (RT.close_term e2 x))

    | T_BindFn _ _ _ c1 c2 b x e1_typing _u t_typing e2_typing c2_typing ->
      let e1 = elab_st_typing e1_typing in
      let e2 = elab_st_typing e2_typing in
      let ty1 = elab_term (comp_res c1) in
      RT.mk_let RT.pp_name_default e1 ty1 (RT.close_term e2 x)
      
    | T_Frame _ _ c frame _frame_typing e_typing ->
      let e = elab_st_typing e_typing in
      elab_frame c frame e
      
    | T_Equiv _ _ c1 c2 e_typing (ST_TotEquiv _ _ _ _ _ _) ->
      let e = elab_st_typing e_typing in
      e

    | T_Equiv _ _ c1 c2 e_typing _ ->
      let e = elab_st_typing e_typing in
      elab_sub c1 c2 e

    | T_Sub _ _ c1 c2 e_typing d_sub ->
      let e = elab_st_typing e_typing in
      let (| coercion, _ |) = elab_st_sub d_sub in
      R.mk_e_app coercion [e]

    | T_Lift _ _ c1 c2 e_typing lc ->
      let e = elab_st_typing e_typing in
      elab_lift lc e

    | T_If _ b _ _ _ _ _ e1_typing e2_typing _c_typing ->
      let rb = elab_term b in
      let re1 = elab_st_typing e1_typing in
      let re2 = elab_st_typing e2_typing in
      RT.mk_if rb re1 re2

    | T_Match _ _ _ sc _ _ _ _ _ brty  _ ->
      let sc = elab_term sc in
      let brs = elab_branches brty in
      R.pack_ln (R.Tv_Match sc None brs)

    | T_IntroPure _ p _ _ ->
      let head = 
        tm_pureapp (tm_fvar (as_fv (mk_pulse_lib_core_lid "intro_pure")))
                       None
                       p
      in
      let arg = (`()) in
      R.mk_app (elab_term head) [(arg, elab_qual None)]

    | T_ElimExists _ u t p _ d_t d_exists ->
      let ru = u in
      let rt = elab_term t in
      let rp = elab_term p in
      mk_elim_exists ru rt (mk_abs rt R.Q_Explicit rp)

    | T_IntroExists _ u b p e _ _ _ ->
      let ru = u in
      let rt = elab_term b.binder_ty in
      let rp = elab_term p in
      let re = elab_term e in
      mk_intro_exists ru rt (mk_abs rt R.Q_Explicit rp) re

    | T_While _ inv _ _ _ cond_typing body_typing ->
      let inv = elab_term inv in
      let cond = elab_st_typing cond_typing in
      let body = elab_st_typing body_typing in
      mk_while (mk_abs bool_tm R.Q_Explicit inv) cond body

    | T_Par _ eL cL eR cR _ _ _ eL_typing eR_typing ->
      let ru = comp_u cL in
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

    | T_WithLocal _ _ init _ init_t c x _ _ _ body_typing ->
      let rret_u = comp_u c in
      let ra = elab_term init_t in
      let rinit = elab_term init in
      let rret_t = elab_term (comp_res c) in
      let rpre = elab_term (comp_pre c) in
      let rpost = mk_abs rret_t R.Q_Explicit (elab_term (comp_post c)) in
      let rbody = elab_st_typing body_typing in
      let rbody = RT.close_term rbody x in
      let rbody = mk_abs (mk_ref ra) R.Q_Explicit rbody in
      mk_withlocal rret_u ra rinit rpre rret_t rpost rbody

    | T_WithLocalArray _ _ init len _ init_t c x _ _ _ _ body_typing ->
      let rret_u = comp_u c in
      let ra = elab_term init_t in
      let rinit = elab_term init in
      let rlen = elab_term len in
      let rret_t = elab_term (comp_res c) in
      let rpre = elab_term (comp_pre c) in
      let rpost = mk_abs rret_t R.Q_Explicit (elab_term (comp_post c)) in
      let rbody = elab_st_typing body_typing in
      let rbody = RT.close_term rbody x in
      let rbody = mk_abs (mk_array ra) R.Q_Explicit rbody in
      mk_withlocalarray rret_u ra rinit rlen rpre rret_t rpost rbody

    | T_Admit _ {u;res;pre;post} c _ ->
      let ru = u in
      let rres = elab_term res in
      let rpre = elab_term pre in
      let rpost = elab_term post in
      let rpost = mk_abs rres R.Q_Explicit rpost in
      (match c with
       | STT -> mk_stt_admit ru rres rpre rpost
       | STT_Atomic -> mk_stt_atomic_admit ru rres rpre rpost
       | STT_Ghost -> mk_stt_ghost_admit ru rres rpre rpost)

    | T_Unreachable _ _ _ _ _ ->
      `("IOU: elab_st_typing of T_Unreachable")

    | T_WithInv _ _ _ _ _ _ _ _ _ ->
      `("IOU: elab_st_typing of T_WithInv")

and elab_br (#g:env)
            (#c:comp_st)
            (#sc_u:universe) (#sc_ty:typ) (#sc:term)
            (#p:pattern)
            (#e:st_term)
            (d : br_typing g sc_u sc_ty sc p e c)
  : Tot R.branch (decreases d)
  = let TBR _ _ _ _ _ _ _ _ bs _ _ _ ed = d in
    let e = elab_st_typing ed in
    (elab_pat p, e)
and elab_branches (#g:env)
                  (#c:comp_st)
                  (#sc_u:universe) (#sc_ty:typ) (#sc:term)
                  (#brs:list branch)
                  (d : brs_typing g sc_u sc_ty sc brs c)
  : Tot (list R.branch)
        (decreases d)
  = match d with
    | TBRS_0 _ -> []
    | TBRS_1 _ p e bd _ d' ->
    elab_br bd :: elab_branches d'
