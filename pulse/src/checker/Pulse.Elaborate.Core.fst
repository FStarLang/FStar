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

module S = Pulse.Syntax
module RU = Pulse.RuntimeUtils
module T = FStar.Tactics.V2
open Pulse.Reflection.Util

let elab_frame (c:comp_st) (frame:term) (e:R.term) =
  let u = comp_u c in
  let ty = comp_res c in
  let pre = comp_pre c in
  let post = comp_post c in
  if C_ST? c
  then mk_frame_stt u ty pre (mk_abs ty R.Q_Explicit post) frame e
  else if C_STAtomic? c
  then let opened = comp_inames c in
       mk_frame_stt_atomic u ty opened pre (mk_abs ty R.Q_Explicit post) frame e
  else mk_frame_stt_ghost u ty pre (mk_abs ty R.Q_Explicit post) frame e

let elab_sub (c1 c2:comp_st) (e:R.term) =
  let ty = comp_res c1 in
  let u = comp_u c1 in
  let pre1 = comp_pre c1 in
  let pre2 = comp_pre c2 in
  let post1 = mk_abs ty R.Q_Explicit (comp_post c1) in
  let post2 = mk_abs ty R.Q_Explicit (comp_post c2) in
  if C_ST? c1
  then mk_sub_stt u ty pre1 pre2 post1 post2 e
  else if C_STAtomic? c1
  then let opened = comp_inames c1 in
       mk_sub_stt_atomic u ty opened pre1 pre2 post1 post2 e
  else mk_sub_stt_ghost u ty pre1 pre2 post1 post2 e


let elab_bind #g #x #c1 #c2 #c
              (bc:bind_comp g x c1 c2 c)
              (e1 e2:R.term)
  : R.term
  = let t1 = comp_res c1 in
    let t2 = comp_res c2 in
    match c1 with
    | C_ST _ ->
      mk_bind_stt
          (comp_u c1)
          (comp_u c2)
          t1 t2
          (comp_pre c1)
          (mk_abs t1 R.Q_Explicit (comp_post c1))
          (mk_abs t2 R.Q_Explicit (comp_post c2))
          e1 e2
    | C_STGhost inames _ ->
        mk_bind_ghost
          (comp_u c1)
          (comp_u c2)
          t1 t2
          inames
          (comp_pre c1)
          (mk_abs t1 R.Q_Explicit (comp_post c1))
          (mk_abs t2 R.Q_Explicit (comp_post c2))
          e1 e2
    | C_STAtomic inames obs1 _ ->
      let C_STAtomic _ obs2 _ = c2 in      
      mk_bind_atomic
          (comp_u c1)
          (comp_u c2)
          (elab_observability obs1)
          (elab_observability obs2)
          (comp_inames c1)
          t1 t2
          (comp_pre c1)
          (mk_abs t1 R.Q_Explicit (comp_post c1))
          (mk_abs t2 R.Q_Explicit (comp_post c2))
          e1 e2
  
let elab_lift #g #c1 #c2 (d:lift_comp g c1 c2) (e:R.term)
  : GTot R.term
  = match d with
    | Lift_STAtomic_ST _ _ ->
      let t = comp_res c1 in
      mk_lift_atomic_stt
        (comp_u c1)
        (comp_res c1)
        t
        (mk_abs t R.Q_Explicit (comp_post c1))
        e

    | Lift_Observability _ c o2 ->
      let t = comp_res c1 in
      mk_lift_observability
        (comp_u c1)
        (elab_observability (C_STAtomic?.obs c))
        (elab_observability o2)
        (comp_inames c1)
        t
        (comp_pre c1)
        (mk_abs t R.Q_Explicit (comp_post c1))
        e
            
    | Lift_Ghost_Neutral _ _ (| reveal_a, reveal_a_typing |) ->
      let t = comp_res c1 in
      mk_lift_ghost_neutral
        (comp_u c1)
        t
        (comp_pre c1)
        (mk_abs t R.Q_Explicit (comp_post c1))
        e
        reveal_a

    | Lift_Neutral_Ghost _ c ->
      let t = comp_res c1 in
      mk_lift_neutral_ghost
        (comp_u c1)
        t
        (comp_pre c1)
        (mk_abs t R.Q_Explicit (comp_post c1))
        e

let intro_pure_tm (p:term) =
  let open Pulse.Reflection.Util in
  let rng = R.range_of_term p in
  wtag (Some STT_Ghost) 
       (Tm_ST
        { t = T.mk_app
                (tm_pureapp (tm_fvar (as_fv (mk_pulse_lib_core_lid "intro_pure")))
                       None
                       p)
                [S.wr (`()) rng, T.Q_Explicit];
          args = [] })

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
  : GTot R.term (decreases d)
  = match d with
    | T_Abs _ x qual b _u body _c ty_typing body_typing ->
      let ty = b.binder_ty in
      let ppname = b.binder_ppname.name in
      let body = elab_st_typing body_typing in
      mk_abs_with_name ppname ty (elab_qual qual) (RT.close_term body x) //this closure should be provably redundant by strengthening the conditions on x

    | T_ST _ t _ _
    | T_STGhost _ t _ _ _ -> t

    | T_Return _ c use_eq u ty t post _ _ _ _ ->
      let rp = mk_abs ty R.Q_Explicit post in
      (match c, use_eq with
       | STT, true -> mk_stt_return u ty t rp
       | STT, false -> mk_stt_return_noeq u ty t rp
       | STT_Atomic, true -> mk_stt_atomic_return u ty t rp
       | STT_Atomic, false -> mk_stt_atomic_return_noeq u ty t rp
       | STT_Ghost, true -> mk_stt_ghost_return u ty t rp
       | STT_Ghost, false -> mk_stt_ghost_return_noeq u ty t rp)

    | T_Bind _ e1 e2 c1 c2 b x c e1_typing t_typing e2_typing bc ->
      let e1 = elab_st_typing e1_typing in
      let e2 = elab_st_typing e2_typing in
      let ty1 = comp_res c1 in
      elab_bind bc e1 (mk_abs_with_name b.binder_ppname.name ty1 R.Q_Explicit (RT.close_term e2 x))

    | T_BindFn _ _ _ c1 c2 b x e1_typing _u t_typing e2_typing c2_typing ->
      let e1 = elab_st_typing e1_typing in
      let e2 = elab_st_typing e2_typing in
      let ty1 = comp_res c1 in
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
      let re1 = elab_st_typing e1_typing in
      let re2 = elab_st_typing e2_typing in
      RT.mk_if b re1 re2

    | T_Match _ _ _ sc _ _ _ _ _ brty  _ ->
      let brs = elab_branches brty in
      R.pack_ln (R.Tv_Match sc None brs)

    | T_IntroPure _ p _ _ ->
      let head = 
        tm_pureapp (tm_fvar (as_fv (mk_pulse_lib_core_lid "intro_pure")))
                       None
                       p
      in
      let arg = (`()) in
      R.mk_app head [(arg, elab_qual None)]

    | T_ElimExists _ u t p _ d_t d_exists ->
      mk_elim_exists u t (mk_abs t R.Q_Explicit p)

    | T_IntroExists _ u b p e _ _ _ ->
      let rt = b.binder_ty in
      mk_intro_exists u rt (mk_abs rt R.Q_Explicit p) e

    | T_While _ inv _ _ _ cond_typing body_typing ->
      let cond = elab_st_typing cond_typing in
      let body = elab_st_typing body_typing in
      mk_while (mk_abs bool_tm R.Q_Explicit inv) cond body

    | T_NuWhile _ inv post _ _ _ _ cond_typing body_typing ->
      let cond = elab_st_typing cond_typing in
      let body = elab_st_typing body_typing in
      mk_nu_while inv (mk_abs bool_tm R.Q_Explicit post) cond body

		| T_Rewrite _ p q _ _ ->
		  mk_rewrite p q

    | T_WithLocal _ _ init _ init_t c x _ _ _ body_typing ->
      let rret_u = comp_u c in
      let rret_t = comp_res c in
      let rpre = comp_pre c in
      let rpost = mk_abs rret_t R.Q_Explicit (comp_post c) in
      let rbody = elab_st_typing body_typing in
      let rbody = RT.close_term rbody x in
      let rbody = mk_abs (mk_ref init_t) R.Q_Explicit rbody in
      mk_withlocal rret_u init_t init rpre rret_t rpost rbody

    | T_WithLocalUninit .. ->
      admit ()

    | T_WithLocalArray _ _ init len _ init_t c x _ _ _ _ body_typing ->
      let rret_u = comp_u c in
      let rret_t = comp_res c in
      let rpre = comp_pre c in
      let rpost = mk_abs rret_t R.Q_Explicit (comp_post c) in
      let rbody = elab_st_typing body_typing in
      let rbody = RT.close_term rbody x in
      let rbody = mk_abs (mk_array init_t) R.Q_Explicit rbody in
      mk_withlocalarray rret_u init_t init len rpre rret_t rpost rbody

    | T_WithLocalArrayUninit .. ->
      admit ()

    | T_Admit _ c _ ->
      let {u; res; pre; post} = st_comp_of_comp c in
      let rpost = mk_abs res R.Q_Explicit post in
      (match c with
       | C_ST _ -> mk_stt_admit u res pre rpost
       | C_STAtomic _ _ _ -> mk_stt_atomic_admit u res pre rpost
       | C_STGhost _ _ -> mk_stt_ghost_admit u res pre rpost)
    
    | T_ForwardJumpLabel .. -> admit ()
    | T_Goto .. -> admit ()

    | T_Unreachable .. ->
      `("IOU: elab_st_typing of T_Unreachable")

and elab_br (#g:env)
            (#c:comp_st)
            (#sc_u:universe) (#sc_ty:typ) (#sc:term)
            (#p:pattern)
            (#e:st_term)
            (d : br_typing g sc_u sc_ty sc p e c)
  : GTot R.branch (decreases d)
  = let TBR _ _ _ _ _ _ _ _ bs _ _ _ ed = d in
    let e = elab_st_typing ed in
    (elab_pat p, e)
and elab_branches (#g:env)
                  (#c:comp_st)
                  (#sc_u:universe) (#sc_ty:typ) (#sc:term)
                  (#brs:list branch)
                  (d : brs_typing g sc_u sc_ty sc brs c)
  : GTot (list R.branch)
        (decreases d)
  = match d with
    | TBRS_0 _ -> []
    | TBRS_1 _ p e bd _ d' ->
    elab_br bd :: elab_branches d'
