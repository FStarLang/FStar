module Pulse.Soundness.Bind
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
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


#push-options "--fuel 2 --ifuel 1 --query_stats"
let inst_bind_t1 #u1 #u2 #g #head
                   (head_typing: RT.typing g head (bind_type u1 u2))
                   (#t1:_)
                   (t1_typing: RT.typing g t1 (RT.tm_type u1))
  : GTot (RT.typing g (R.mk_app head [(t1, R.Q_Implicit)]) (bind_type_t1 u1 u2 t1))
  = let open_with_spec (t v:R.term)
      : Lemma (RT.open_with t v == RT.open_or_close_term' t (RT.OpenWith v) 0)
              [SMTPat (RT.open_with t v)]
      = RT.open_with_spec t v
    in
    let d : RT.typing g (R.mk_app head [(t1, R.Q_Implicit)]) _ =
      RT.T_App _ _ _ _ _ head_typing t1_typing
    in
    assume (bind_type_t1 u1 u2 t1 ==
            RT.open_with (RT.open_or_close_term' (bind_type_t1 u1 u2 (mk_name 4))
                                                 (RT.CloseVar 4) 0)
                         t1);

    d
#pop-options

let inst_bind_t2 #u1 #u2 #g #head #t1
                   (head_typing: RT.typing g head (bind_type_t1 u1 u2 t1))
                   (#t2:_)
                   (t2_typing: RT.typing g t2 (RT.tm_type u2))
  : RT.typing g (R.mk_app head [(t2, R.Q_Implicit)]) (bind_type_t1_t2 u1 u2 t1 t2)
  = admit()


let inst_bind_pre #u1 #u2 #g #head #t1 #t2
                  (head_typing: RT.typing g head (bind_type_t1_t2 u1 u2 t1 t2))
                  (#pre:_)
                  (pre_typing: RT.typing g pre vprop_tm)
  : RT.typing g (R.mk_app head [(pre, R.Q_Implicit)]) (bind_type_t1_t2_pre u1 u2 t1 t2 pre)
  = admit()

let inst_bind_post1 #u1 #u2 #g #head #t1 #t2 #pre
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre u1 u2 t1 t2 pre))
                  (#post1:_)
                  (post1_typing: RT.typing g post1 (post1_type_bind t1))
  : RT.typing g (R.mk_app head [(post1, R.Q_Implicit)]) (bind_type_t1_t2_pre_post1 u1 u2 t1 t2 pre post1)
  = admit()

let inst_bind_post2 #u1 #u2 #g #head #t1 #t2 #pre #post1
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre_post1 u1 u2 t1 t2 pre post1))
                  (#post2:_)
                  (post2_typing: RT.typing g post2 (post2_type_bind t2))
  : RT.typing g (R.mk_app head [(post2, R.Q_Implicit)]) (bind_type_t1_t2_pre_post1_post2 u1 u2 t1 t2 pre post1 post2)
  = admit()

let inst_bind_f #u1 #u2 #g #head #t1 #t2 #pre #post1 #post2
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre_post1_post2 u1 u2 t1 t2 pre post1 post2))
                  (#f:_)
                  (f_typing: RT.typing g f (mk_stt_comp u1 t1 pre post1))
  : RT.typing g (R.mk_app head [(f, R.Q_Explicit)]) (bind_type_t1_t2_pre_post1_post2_f u1 u2 t1 t2 pre post1 post2)
  = admit()

let inst_bind_g #u1 #u2 #g #head #t1 #t2 #pre #post1 #post2
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre_post1_post2_f u1 u2 t1 t2 pre post1 post2))
                  (#gg:_)
                  (g_typing: RT.typing g gg (g_type_bind u2 t1 t2 post1 post2))
  : RT.typing g (R.mk_app head [(gg, R.Q_Explicit)]) (bind_res u2 t2 pre post2)
  = let open_with_spec (t v:R.term)
      : Lemma (RT.open_with t v == RT.open_or_close_term' t (RT.OpenWith v) 0)
              [SMTPat (RT.open_with t v)]
      = RT.open_with_spec t v
    in
    let d : RT.typing g (R.mk_app head [(gg, R.Q_Explicit)]) _ =
      RT.T_App _ _ _ _ _ head_typing g_typing
    in
    admit();
    d
#pop-options

#push-options "--z3rlimit_factor 8"
let elab_bind_typing (f:stt_env)
                     (g:env)
                     (c1 c2 c:ln_comp)
                     (x:var { ~ (x `Set.mem` freevars_comp c1) })
                     (r1:R.term)
                     (r1_typing: RT.typing (extend_env_l f g) r1 (elab_comp c1))
                     (r2:R.term)
                     (r2_typing: RT.typing (extend_env_l f g) r2 
                                           (elab_term (Tm_Arrow (null_binder (comp_res c1)) None (close_comp c2 x))))
                     (bc:bind_comp f g x c1 c2 c)
                     (t2_typing : RT.typing (extend_env_l f g) (elab_term (comp_res c2)) (RT.tm_type (elab_universe (comp_u c2))))
                     (post2_typing: RT.typing (extend_env_l f g) 
                                              (elab_comp_post c2)
                                              (post2_type_bind (elab_term (comp_res c2))))
  = assume (C_ST? c1 /\ C_ST? c2);
    let rg = extend_env_l f g in
    let u1 = elab_universe (comp_u c1) in
    let u2 = elab_universe (comp_u c2) in
    let bind_lid = mk_steel_wrapper_lid "bind_stt" in
    let bind_fv = R.pack_fv bind_lid in
    let head = R.pack_ln (R.Tv_UInst bind_fv [u1;u2]) in
    assume (RT.lookup_fvar_uinst rg bind_fv [u1; u2] == Some (bind_type u1 u2));
    let head_typing : RT.typing _ _ (bind_type u1 u2) = RT.T_UInst rg bind_fv [u1;u2] in
    let (| _, c1_typing |) = RT.type_correctness _ _ _ r1_typing in
    let t1_typing, pre_typing, post_typing = inversion_of_stt_typing _ _ _ _ c1_typing in
    let t1 = (elab_term (comp_res c1)) in
    let t2 = (elab_term (comp_res c2)) in
    let t1_typing : RT.typing rg t1 (RT.tm_type u1) = t1_typing in
    let post1 = elab_comp_post c1 in
    let c2_x = close_comp c2 x in
    assume (comp_res c2_x == comp_res c2);
    assume (comp_post c2_x == comp_post c2);    
    assert (open_term (comp_post c1) x == comp_pre c2);
    assert (~ (x `Set.mem` freevars (comp_post c1)));
    close_open_inverse (comp_post c1) x;
    assert (comp_post c1 == close_term (comp_pre c2) x);
    assert (post1 == mk_abs t1 R.Q_Explicit (elab_term (comp_post c1)));
    assert (elab_term (comp_post c1) == elab_term (comp_pre (close_comp c2 x)));
    //ln (comp_post c1) 0
    let g_typing
      : RT.typing _ _ 
                  (mk_arrow (t1, R.Q_Explicit)
                            (mk_stt_comp u2 t2 (elab_term (comp_post c1)) (elab_comp_post c2)))
      = r2_typing in
    let g_typing 
      : RT.typing _ _ 
                  (mk_arrow (t1, R.Q_Explicit)
                            (mk_stt_comp u2 t2
                                            (R.mk_app (mk_abs t1 R.Q_Explicit (elab_term (comp_post c1)))
                                                     [bound_var 0, R.Q_Explicit])
                                                (elab_comp_post c2)))
      = RT.(T_Sub _ _ _ _ r2_typing (ST_Equiv _ _ _ (mequiv_arrow _ _ _ _ _ _))) in
    let d : RT.typing _ (elab_bind bc r1 r2) _ = 
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

let elab_bind_ghost_l_typing f g c1 c2 c x r1 r1_typing r2 r2_typing bc t2_typing post2_typing
  reveal_a reveal_a_typing =
  admit ()

let elab_bind_ghost_r_typing f g c1 c2 c x r1 r1_typing r2 r2_typing bc t2_typing post2_typing
  reveal_b reveal_b_typing =
  admit ()
