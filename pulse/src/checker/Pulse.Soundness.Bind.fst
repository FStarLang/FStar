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

module Pulse.Soundness.Bind
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

#push-options "--z3rlimit_factor 5"
(*** Soundness of bind elaboration *)


(* x:t1 -> stt t2 pre post   ~    x:t1 -> stt t2 ((fun x -> pre) x) post *)
let mequiv_arrow (g:R.env) (t1:R.term) (u2:R.universe) (t2:R.term) (pre:R.term) (post:R.term) //need some ln preconditions
  : GTot (RT.equiv g (mk_arrow (t1, R.Q_Explicit)
                               (mk_stt_comp u2 t2 pre post))
                     (mk_arrow (t1, R.Q_Explicit)
                               (mk_stt_comp u2 t2 (R.mk_app (mk_abs t1 R.Q_Explicit pre) [bound_var 0, R.Q_Explicit]) post)))
  = admit()


#push-options "--fuel 2 --ifuel 1"
let inst_bind_t1 #u1 #u2 #g #head
                   (head_typing: RT.tot_typing g head (bind_type u1 u2))
                   (#t1:_)
                   (t1_typing: RT.tot_typing g t1 (RT.tm_type u1))
  : GTot (RT.tot_typing g (R.mk_app head [(t1, R.Q_Implicit)]) (bind_type_t1 u1 u2 t1))
  = let open_with_spec (t v:R.term)
      : Lemma (RT.open_with t v == RT.subst_term t [ RT.DT 0 v ])
              [SMTPat (RT.open_with t v)]
      = RT.open_with_spec t v
    in
    let d : RT.tot_typing g (R.mk_app head [(t1, R.Q_Implicit)]) _ =
      RT.T_App _ _ _ _
        (RT.subst_term (bind_type_t1 u1 u2 (mk_name 4)) [ RT.ND 4 0 ])
        _ head_typing t1_typing
    in
    assume (bind_type_t1 u1 u2 t1 ==
            RT.open_with (RT.subst_term (bind_type_t1 u1 u2 (mk_name 4))
                                        [ RT.ND 4 0 ])
                         t1);

    d
#pop-options

let inst_bind_t2 #u1 #u2 #g #head #t1
                   (head_typing: RT.tot_typing g head (bind_type_t1 u1 u2 t1))
                   (#t2:_)
                   (t2_typing: RT.tot_typing g t2 (RT.tm_type u2))
  : RT.tot_typing g (R.mk_app head [(t2, R.Q_Implicit)]) (bind_type_t1_t2 u1 u2 t1 t2)
  = admit()


let inst_bind_pre #u1 #u2 #g #head #t1 #t2
                  (head_typing: RT.tot_typing g head (bind_type_t1_t2 u1 u2 t1 t2))
                  (#pre:_)
                  (pre_typing: RT.tot_typing g pre slprop_tm)
  : RT.tot_typing g (R.mk_app head [(pre, R.Q_Implicit)]) (bind_type_t1_t2_pre u1 u2 t1 t2 pre)
  = admit()

let inst_bind_post1 #u1 #u2 #g #head #t1 #t2 #pre
                  (head_typing: RT.tot_typing g head (bind_type_t1_t2_pre u1 u2 t1 t2 pre))
                  (#post1:_)
                  (post1_typing: RT.tot_typing g post1 (post1_type_bind t1))
  : RT.tot_typing g (R.mk_app head [(post1, R.Q_Implicit)]) (bind_type_t1_t2_pre_post1 u1 u2 t1 t2 pre post1)
  = admit()

let inst_bind_post2 #u1 #u2 #g #head #t1 #t2 #pre #post1
                  (head_typing: RT.tot_typing g head (bind_type_t1_t2_pre_post1 u1 u2 t1 t2 pre post1))
                  (#post2:_)
                  (post2_typing: RT.tot_typing g post2 (post2_type_bind t2))
  : RT.tot_typing g (R.mk_app head [(post2, R.Q_Implicit)]) (bind_type_t1_t2_pre_post1_post2 u1 u2 t1 t2 pre post1 post2)
  = admit()

let inst_bind_f #u1 #u2 #g #head #t1 #t2 #pre #post1 #post2
                  (head_typing: RT.tot_typing g head (bind_type_t1_t2_pre_post1_post2 u1 u2 t1 t2 pre post1 post2))
                  (#f:_)
                  (f_typing: RT.tot_typing g f (mk_stt_comp u1 t1 pre post1))
  : RT.tot_typing g (R.mk_app head [(f, R.Q_Explicit)]) (bind_type_t1_t2_pre_post1_post2_f u1 u2 t1 t2 pre post1 post2)
  = admit()

let inst_bind_g #u1 #u2 #g #head #t1 #t2 #pre #post1 #post2
                  (head_typing: RT.tot_typing g head (bind_type_t1_t2_pre_post1_post2_f u1 u2 t1 t2 pre post1 post2))
                  (#gg:_)
                  (g_typing: RT.tot_typing g gg (g_type_bind u2 t1 t2 post1 post2))
  : RT.tot_typing g (R.mk_app head [(gg, R.Q_Explicit)]) (bind_res u2 t2 pre post2)
  = let open_with_spec (t v:R.term)
      : Lemma (RT.open_with t v == RT.subst_term t [ RT.DT 0 v ])
              [SMTPat (RT.open_with t v)]
      = RT.open_with_spec t v
    in
    let d : RT.tot_typing g (R.mk_app head [(gg, R.Q_Explicit)]) _ =
      RT.T_App _ _ _ _ (bind_res u2 t2 pre post2) _ head_typing g_typing
    in
    admit();
    d
#pop-options

#push-options "--z3rlimit_factor 8"
let elab_bind_typing (g:stt_env)
                     (c1 c2 c:ln_comp)
                     (x:var { ~ (x `Set.mem` freevars_comp c1) })
                     (r1:R.term)
                     (r1_typing: RT.tot_typing (elab_env g) r1 (elab_comp c1))
                     (r2:R.term)
                     (r2_typing: RT.tot_typing (elab_env g) r2 
                                               (tm_arrow (null_binder (comp_res c1)) None (close_comp c2 x)))
                     (bc:bind_comp g x c1 c2 c)
                     (t2_typing : RT.tot_typing (elab_env g) (comp_res c2) (RT.tm_type (comp_u c2)))
                     (post2_typing: RT.tot_typing (elab_env g) 
                                                  (elab_comp_post c2)
                                                  (post2_type_bind (comp_res c2)))
  = assume (C_ST? c1 /\ C_ST? c2);
    let rg = elab_env g in
    let u1 = comp_u c1 in
    let u2 = comp_u c2 in
    let bind_lid = mk_pulse_lib_core_lid "bind_stt" in
    let bind_fv = R.pack_fv bind_lid in
    let head = R.pack_ln (R.Tv_UInst bind_fv [u1;u2]) in
    assume (RT.lookup_fvar_uinst rg bind_fv [u1; u2] == Some (bind_type u1 u2));
    let head_typing : RT.tot_typing _ _ (bind_type u1 u2) = RT.T_UInst rg bind_fv [u1;u2] in
    let (| _, c1_typing |) = RT.type_correctness _ _ _ r1_typing in
    let t1_typing, pre_typing, post_typing = inversion_of_stt_typing _ _ c1_typing in
    let t1 = (comp_res c1) in
    let t2 = (comp_res c2) in
    let t1_typing : RT.tot_typing rg t1 (RT.tm_type u1) = t1_typing in
    let post1 = elab_comp_post c1 in
    let c2_x = close_comp c2 x in
    assume (comp_res c2_x == comp_res c2);
    assume (comp_post c2_x == comp_post c2);    
    assert (open_term (comp_post c1) x == comp_pre c2);
    assert (~ (x `Set.mem` freevars (comp_post c1)));
    close_open_inverse (comp_post c1) x;
    assert (comp_post c1 == close_term (comp_pre c2) x);
    assert (post1 == mk_abs t1 R.Q_Explicit (comp_post c1));
    assert (comp_post c1 == comp_pre (close_comp c2 x));
    //ln (comp_post c1) 0
    let g_typing
      : RT.tot_typing _ _ 
                  (mk_arrow (t1, R.Q_Explicit)
                            (mk_stt_comp u2 t2 (comp_post c1) (elab_comp_post c2)))
       = r2_typing in
    let g_typing 
      : RT.tot_typing _ _ 
                  (mk_arrow (t1, R.Q_Explicit)
                            (mk_stt_comp u2 t2
                                            (R.mk_app (mk_abs t1 R.Q_Explicit (comp_post c1))
                                                     [bound_var 0, R.Q_Explicit])
                                                (elab_comp_post c2)))
      = RT.T_Sub _ _ _ _ r2_typing
          (RT.Relc_typ _ _ _ _ _
             (RT.Rel_equiv _ _ _ _ (mequiv_arrow _ _ _ _ _ _)))
        in
    let d : RT.tot_typing _ (elab_bind bc r1 r2) _ = 
       inst_bind_g 
        (inst_bind_f
          (inst_bind_post2
            (inst_bind_post1
              (inst_bind_pre 
                (inst_bind_t2 
                  (inst_bind_t1 head_typing t1_typing)
                  t2_typing)
                pre_typing)
              post_typing)
            post2_typing)
          r1_typing)
        g_typing
    in
    d
#pop-options

#push-options "--z3rlimit_factor 4 --split_queries no"
assume
val open_close_inverse_t (e:R.term { RT.ln e }) (x:var) (t:R.term)
  : Lemma (RT.open_with (RT.close_term e x) t == e)

let bind_fn_typing #g #t #c d soundness =
  let T_BindFn _ e1 e2 c1 c2 b x e1_typing u t1_typing e2_typing c2_typing = d in
  let t1 = comp_res c1 in
  let g_x = push_binding g x ppname_default t1 in

  let re1 = elab_st_typing e1_typing in
  let re2 = elab_st_typing e2_typing in

  let re1_typing : RT.tot_typing (elab_env g) re1 t1 =
    soundness g e1 c1 e1_typing in
  
  let re2_typing : RT.tot_typing (elab_env g_x) re2 (elab_comp c2) =
    soundness g_x (open_st_term_nv e2 (v_as_nv x)) c2 e2_typing in

  RT.well_typed_terms_are_ln _ _ _ re2_typing;
  calc (==) {
    RT.open_term (RT.close_term re2 x) x;
       (==) { RT.open_term_spec (RT.close_term re2 x) x }
    RT.subst_term (RT.close_term re2 x) (RT.open_with_var x 0);
       (==) { RT.close_term_spec re2 x }
    RT.subst_term (RT.subst_term re2 [ RT.ND x 0 ]) (RT.open_with_var x 0);
       (==) { RT.open_close_inverse' 0 re2 x }
    re2;
  };
  let elab_t = RT.mk_let RT.pp_name_default re1 t1 (RT.close_term re2 x) in
  let res
    : RT.tot_typing (elab_env g) elab_t (RT.open_with (RT.close_term (elab_comp c2) x) re1)
    = RT.T_Let (elab_env g) x re1 t1 (RT.close_term re2 x) (elab_comp c2) T.E_Total RT.pp_name_default re1_typing re2_typing in
  Pulse.Typing.LN.comp_typing_ln c2_typing;
  Pulse.Elaborate.elab_ln_comp c (-1);
  assert (RT.ln (elab_comp c2));
  open_close_inverse_t (elab_comp c2) x re1;
  assert (RT.open_with (RT.close_term (elab_comp c2) x) re1 == elab_comp c2); 
  res
  

