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

module Pulse.Soundness
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
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
module WithLocal = Pulse.Soundness.WithLocal
module WithLocalArray = Pulse.Soundness.WithLocalArray
module Rewrite = Pulse.Soundness.Rewrite
module Comp = Pulse.Soundness.Comp
module LN = Pulse.Typing.LN
module FV = Pulse.Typing.FV
module Sub = Pulse.Soundness.Sub
module RU = Pulse.RuntimeUtils
module Typing = Pulse.Typing

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
            (mk_abs_with_name ppname.name ty (elab_qual q) (RT.close_term (elab_st_typing body_typing) x))
            (tm_arrow (mk_binder_ppname ty ppname) q (close_comp c x)))

#push-options "--z3rlimit_factor 4 --split_queries no"
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
    Lift.elab_lift_stt_atomic_st_typing g
      c1 c2 _ (soundness _ _ _ e_typing) lc

  | Lift_Ghost_Neutral _ _ w ->
    let (| reveal_a, reveal_a_typing |) = w in
    Lift.elab_lift_ghost_neutral_typing g
      c1 c2 _ (soundness _ _ _ e_typing) lc
      _ (tot_typing_soundness reveal_a_typing)

  | Lift_Neutral_Ghost _ _ ->
    Lift.elab_lift_neutral_ghost_typing g
      c1 c2 _ (soundness _ _ _ e_typing) lc

  | Lift_Observability _ _ _ ->
    Lift.elab_lift_observability_typing g
      c1 c2 _ (soundness _ _ _ e_typing) lc
#pop-options

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
  match equiv with
  | ST_TotEquiv _ t1 t2 _ _ eq ->
    let r_e_typing : RT.tot_typing (elab_env g) (elab_st_typing e_typing) t1 = 
        r_e_typing
    in
    let eq = RT.Rel_equiv _ _ _ RT.R_Sub eq in
    RT.T_Sub _ _ _ _ r_e_typing (RT.Relc_typ _ _ _ _ _ eq)
  | _ ->  
    STEquiv.st_equiv_soundness _ _ _ equiv _ r_e_typing


#push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 30"

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
      : RT.tot_typing _ _ (tm_arrow (null_binder (comp_res c1)) None (close_comp c2 x))
      = mk_t_abs None _ t_typing e2_typing
    in
    match bc with
    | Bind_comp _ _ _ _ t2_typing y post2_typing ->
         Bind.elab_bind_typing g _ _ _ x _ r1_typing _ r2_typing bc 
                               (tot_typing_soundness t2_typing)
                               (mk_t_abs_tot _ ppname_default t2_typing post2_typing)
#pop-options

#push-options "--z3rlimit_factor 4 --fuel 4 --ifuel 2"
let retype_hyp #g #hyp #t0 #t1 #e #t 
      (_:RT.tot_typing (RT.extend_env g hyp t0) e t)
      (equiv:RT.equiv g t0 t1)
: GTot (RT.tot_typing (RT.extend_env g hyp t1) e t)
= admit()

let equiv_rw #u #t #x #y g
: GTot (RT.equiv g (mk_sq_rewrites_to_p u t x y) (RT.eq2 u t x y))
= admit()

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

  let T_If _ b e1 e2  _ hyp b_typing e1_typing e2_typing (E c_typing) = d in
  let rb_typing : RT.tot_typing (elab_env g)
                                b
                                RT.bool_ty =
    tot_typing_soundness b_typing in
  let g_then = g_with_eq g hyp b tm_true in
  let rw_true = (mk_sq_rewrites_to_p u0 tm_bool b tm_true) in
  elab_push_binding g hyp rw_true;
  let re1_typing
    : RT.tot_typing (RT.extend_env (elab_env g)
                               hyp
                                 (RT.eq2 u0 tm_bool b tm_true))
                (elab_st_typing e1_typing)
                (elab_comp c) =
    retype_hyp (soundness g_then e1 c e1_typing) (equiv_rw _) in
  let g_else = g_with_eq g hyp b tm_false in
  let rw_false = (mk_sq_rewrites_to_p u0 tm_bool b tm_false) in
  elab_push_binding g hyp rw_false;
  let re2_typing
    : RT.tot_typing (RT.extend_env (elab_env g)
                               hyp
                               (RT.eq2 u0 tm_bool b tm_false))
                (elab_st_typing e2_typing)
                (elab_comp c) =
    retype_hyp (soundness g_else e2 c e2_typing) (equiv_rw _) in
  let c_typing = 
    ct_soundness _ _ _ c_typing
  in
  assume (~(hyp `Set.mem` RT.freevars (elab_st_typing e1_typing)));
  assume (~(hyp `Set.mem` RT.freevars (elab_st_typing e2_typing)));  
  RT.T_If _ _ _ _ _ _ _ _ _ rb_typing re1_typing re2_typing c_typing
#pop-options

#push-options "--fuel 2 --ifuel 2"
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
                (mk_abs_with_name ppname.name ty (elab_qual q) (RT.close_term (elab_st_typing body_typing) x))
                (tm_arrow (mk_binder_ppname ty ppname) q (close_comp c x)))
      = let r_t_typing = tot_typing_soundness t_typing in
        let r_body_typing = soundness _ _ _ body_typing in
        mk_t_abs g #_ #_ #_ #t_typing ppname r_t_typing r_body_typing
    in
    LN.st_typing_ln d;
    match d with
    | T_Lift .. ->
      lift_soundness _ _ _ d soundness
    | T_Frame .. ->
      frame_soundness _ _ _ d soundness

    | T_Abs _ x q ty u body c t_typing body_typing ->
      mk_t_abs q ppname_default t_typing body_typing    

    | T_ST ..
    | T_STGhost .. -> admit()

    | T_Bind .. ->
      bind_soundness d soundness mk_t_abs

    | T_BindFn .. ->
      Bind.bind_fn_typing d soundness

    | T_Equiv .. ->
      stequiv_soundness _ _ _ d soundness

    | T_Return .. ->
      Return.return_soundness d

    | T_If .. ->
      let ct_soundness g c uc (d':_ {d' << d}) =
        Comp.comp_typing_soundness g c uc d'
      in
      if_soundness _ _ _ d soundness ct_soundness

    | T_Match .. ->
      let ct_soundness g c uc (d':_ {d' << d}) =
        Comp.comp_typing_soundness g c uc d'
      in
      Pulse.Soundness.Match.match_soundness _ _ _ d soundness ct_soundness

    | T_IntroPure .. ->
      admit()
      
    | T_ElimExists .. ->
      Exists.elim_exists_soundness d

    | T_IntroExists .. ->
      Exists.intro_exists_soundness d

    | T_While .. ->
      While.while_soundness d soundness
    | T_NuWhile .. ->
      admit()

    | T_WithLocal .. ->
      WithLocal.withlocal_soundness d soundness

    | T_WithLocalArray .. ->
      WithLocalArray.withlocalarray_soundness d soundness

    | T_Rewrite .. ->
      Rewrite.rewrite_soundness d

    | T_Admit .. -> Admit.admit_soundess d

    | T_Unreachable .. -> RU.magic()

    | T_Sub .. -> Sub.sub_soundness d soundness
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
