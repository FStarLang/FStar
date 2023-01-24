module Pulse.Soundness.STEquiv
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


let stt_vprop_equiv_closing (t0 t1:R.term) (x:var)
  : Lemma (RT.close_term (stt_vprop_equiv t0 t1) x ==
           stt_vprop_equiv (RT.close_term t0 x) (RT.close_term t1 x))
           [SMTPat (RT.close_term (stt_vprop_equiv t0 t1) x)]
  = RT.close_term_spec (stt_vprop_equiv t0 t1) x;
    RT.close_term_spec t0 x;
    RT.close_term_spec t1 x

let app0 t = R.mk_app t [bound_var 0, R.Q_Explicit]

let abs_and_app0 (ty:R.term) (b:R.term) =
    R.mk_app (mk_abs ty R.Q_Explicit b) [bound_var 0, R.Q_Explicit]


// x:ty -> vprop_equiv p q ~ x:ty -> vprop_equiv ((fun y -> p) x) ((fun y -> q) x)
let stt_vprop_equiv_abstract (#f:stt_env) (#g:env) (#post0 #post1:pure_term) (#pf:_) (#ty:_)
                             (d:RT.typing (extend_env_l f g) pf 
                                          (mk_tot_arrow1 (ty, R.Q_Explicit)
                                                         (stt_vprop_equiv (elab_pure post0) (elab_pure post1))))
  : GTot (RT.typing (extend_env_l f g) pf
                    (mk_tot_arrow1 (ty, R.Q_Explicit)
                                   (stt_vprop_equiv (abs_and_app0 ty (elab_pure post0))
                                                    (abs_and_app0 ty (elab_pure post1)))))
  = admit()

let inst_intro_vprop_post_equiv (#g:R.env) (#ty:R.term) (#u:_)
                                (d_ty:RT.typing g ty (RT.tm_type u))
                                (#post0 #post1:R.term)
                                (d_0:RT.typing g post0 
                                                (mk_tot_arrow1 (ty, R.Q_Explicit) (elab_pure Tm_VProp)))
                                (d_1:RT.typing g post1 
                                                (mk_tot_arrow1 (ty, R.Q_Explicit) (elab_pure Tm_VProp)))
                                (#pf:_)
                                (eq:RT.typing g pf (mk_tot_arrow1 (ty, R.Q_Explicit) 
                                                                 (stt_vprop_equiv (app0 post0) (app0 post1))))
  : GTot ( pf: R.term &
           RT.typing g pf (stt_vprop_post_equiv u ty post0 post1) )
  = admit()


let stt_vprop_post_equiv_is_prop (#g:R.env) (#ty:R.term) (#u:_)
                                 (d_ty:RT.typing g ty (RT.tm_type u))
                                 (#post0 #post1:R.term)
                                 (d_0:RT.typing g post0 
                                                (mk_tot_arrow1 (ty, R.Q_Explicit) (elab_pure Tm_VProp)))
                                 (d_1:RT.typing g post1 
                                                (mk_tot_arrow1 (ty, R.Q_Explicit) (elab_pure Tm_VProp)))
  : GTot (RT.typing g (stt_vprop_post_equiv u ty post0 post1) RT.tm_prop)
  = admit()

let inst_sub_stt (#g:R.env) (#u:_) (#a #pre1 #pre2 #post1 #post2 #r:R.term)
                 (d_a: RT.typing g a (RT.tm_type u))
                 (d_pre1: RT.typing g pre1 (elab_pure Tm_VProp))
                 (d_pre2: RT.typing g pre2 (elab_pure Tm_VProp))
                 (d_post1:RT.typing g post1 (mk_tot_arrow1 (a, R.Q_Explicit) (elab_pure Tm_VProp)))
                 (d_post2:RT.typing g post2 (mk_tot_arrow1 (a, R.Q_Explicit) (elab_pure Tm_VProp)))
                 (pre_equiv:RT.typing g (`()) (stt_vprop_equiv pre1 pre2))
                 (post_equiv:RT.typing g (`()) (stt_vprop_post_equiv u a post1 post2))
                 (d_r:RT.typing g r (mk_stt_app u [a;pre1;post1]))
  : GTot (RT.typing g (mk_sub_stt u a pre1 pre2 post1 post2 r) (mk_stt_app u [a;pre2;post2]))
  = admit()

let vprop_arrow (t:pure_term) : pure_term = Tm_Arrow (null_binder t) None (C_Tot Tm_VProp)

#push-options "--fuel 2 --ifuel 1 --z3rlimit_factor 4 --query_stats"
let st_equiv_soundness (f:stt_env)
                       (g:env)
                       (c0 c1:ln_comp) 
                       (d:st_equiv f g c0 c1)
                       (r:R.term)
                       (d_r:RT.typing (extend_env_l f g) r (elab_pure_comp c0)) 
  : GTot (RT.typing (extend_env_l f g) (elab_sub c0 c1 r) (elab_pure_comp c1))
  = if C_ST? c0 && C_ST? c1 then
    let ST_VPropEquiv _ _ _ x pre_typing res_typing post_typing eq_pre eq_post = d in
    // assert (None? (lookup_ty g x));
    assert (None? (lookup g x));
    assume (~(x `Set.mem` RT.freevars (elab_pure (comp_post c0))));
    assume (~(x `Set.mem` RT.freevars (elab_pure (comp_post c1))));      
    let open_term_spec (e:R.term) (x:var)
        : Lemma 
          (RT.open_term e x == RT.open_or_close_term' e (RT.open_with_var x) 0)
          [SMTPat (RT.open_term e x)]
        = RT.open_term_spec e x
    in
    let pre_equiv = VPropEquiv.vprop_equiv_unit_soundness pre_typing eq_pre in
    let g' = ((x, Inl (comp_res c0))::g) in
    elab_open_commute (comp_post c0) x;
    elab_open_commute (comp_post c1) x;      
    let post_equiv
      : RT.typing (RT.extend_env (extend_env_l f g) x (elab_pure (comp_res c0)))
                  (`())
                  (stt_vprop_equiv 
                    (RT.open_term (elab_pure (comp_post c0)) x)
                    (RT.open_term (elab_pure (comp_post c1)) x))
        = VPropEquiv.vprop_equiv_unit_soundness post_typing eq_post
    in
    let t0 = elab_pure (comp_res c0)  in
    let r_res_typing = tot_typing_soundness res_typing in
    RT.close_open_inverse (elab_pure (comp_post c0)) x;
    RT.close_open_inverse (elab_pure (comp_post c1)) x;      
    let d 
      : RT.typing (extend_env_l f g) _ 
                  (mk_tot_arrow1 (t0, R.Q_Explicit)
                                 (stt_vprop_equiv (elab_pure (comp_post c0))
                                                  (elab_pure (comp_post c1))))
        = RT.T_Abs _ _ _ (`()) _ _ _ R.Q_Explicit
                 r_res_typing
                 post_equiv
    in
    let d = stt_vprop_equiv_abstract d in
    let abs_post0_typing
      : RT.typing (extend_env_l f g)
                  (elab_comp_post c0) // mk_abs t0 (elab_pure (comp_post c0)))
                  (elab_pure (vprop_arrow (comp_res c0)))
      = mk_t_abs_tot _ _ _ res_typing post_typing
    in
    let abs_post1_typing
      : RT.typing (extend_env_l f g)
                  (elab_comp_post c1) //mk_abs t0 (elab_pure (comp_post c1)))
                  (elab_pure (vprop_arrow (comp_res c0)))
      = mk_t_abs_tot _ _ _ res_typing (fst (vprop_equiv_typing _ _ _ _ eq_post) post_typing)
    in
    let (| pf, d |) =
      inst_intro_vprop_post_equiv r_res_typing abs_post0_typing abs_post1_typing d in
    let post_equiv =
        RT.T_PropIrrelevance _ _ _ d 
                             (stt_vprop_post_equiv_is_prop r_res_typing abs_post0_typing abs_post1_typing)
    in
    inst_sub_stt r_res_typing 
                 (tot_typing_soundness pre_typing)
                 (tot_typing_soundness (fst (vprop_equiv_typing _ _ _ _ eq_pre) pre_typing))
                 abs_post0_typing
                 abs_post1_typing
                 pre_equiv
                 post_equiv
                 d_r
    else admit ()
#pop-options
