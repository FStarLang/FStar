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

module Pulse.Soundness.STEquiv
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Elaborate
open Pulse.Soundness.Common
open Pulse.Checker.SLPropEquiv


let stt_slprop_equiv_closing (t0 t1:R.term) (x:var)
  : Lemma (RT.close_term (stt_slprop_equiv t0 t1) x ==
           stt_slprop_equiv (RT.close_term t0 x) (RT.close_term t1 x))
           [SMTPat (RT.close_term (stt_slprop_equiv t0 t1) x)]
  = RT.close_term_spec (stt_slprop_equiv t0 t1) x;
    RT.close_term_spec t0 x;
    RT.close_term_spec t1 x

let app0 t = R.mk_app t [bound_var 0, R.Q_Explicit]

let abs_and_app0 (ty:R.term) (b:R.term) =
    R.mk_app (mk_abs ty R.Q_Explicit b) [bound_var 0, R.Q_Explicit]


// x:ty -> slprop_equiv p q ~ x:ty -> slprop_equiv ((fun y -> p) x) ((fun y -> q) x)
let stt_slprop_equiv_abstract (#g:stt_env) (#post0 #post1:term) (#pf:_) (#ty:_)
                             (d:RT.tot_typing (elab_env g) pf 
                                  (mk_arrow (ty, R.Q_Explicit)
                                     (stt_slprop_equiv post0 post1)))
  : GTot (RT.tot_typing (elab_env g) pf
            (mk_arrow (ty, R.Q_Explicit)
                      (stt_slprop_equiv (abs_and_app0 ty post0)
                                       (abs_and_app0 ty post1))))
  = admit()

let inst_intro_slprop_post_equiv (#g:R.env) (#ty:R.term) (#u:_)
                                (d_ty:RT.tot_typing g ty (RT.tm_type u))
                                (#post0 #post1:R.term)
                                (d_0:RT.tot_typing g post0 
                                       (mk_arrow (ty, R.Q_Explicit) tm_slprop))
                                (d_1:RT.tot_typing g post1 
                                       (mk_arrow (ty, R.Q_Explicit) tm_slprop))
                                (#pf:_)
                                (eq:RT.tot_typing g pf (mk_arrow (ty, R.Q_Explicit) 
                                      (stt_slprop_equiv (app0 post0) (app0 post1))))
  : GTot ( pf: R.term &
           RT.tot_typing g pf (stt_slprop_post_equiv u ty post0 post1) )
  = admit()


let stt_slprop_post_equiv_is_prop (#g:R.env) (#ty:R.term) (#u:_)
                                 (d_ty:RT.tot_typing g ty (RT.tm_type u))
                                 (#post0 #post1:R.term)
                                 (d_0:RT.tot_typing g post0 
                                                (mk_arrow (ty, R.Q_Explicit) tm_slprop))
                                 (d_1:RT.tot_typing g post1 
                                                (mk_arrow (ty, R.Q_Explicit) tm_slprop))
  : GTot (RT.tot_typing g (stt_slprop_post_equiv u ty post0 post1) RT.tm_prop)
  = admit()

let inst_sub_stt (#g:R.env) (#u:_) (#a #pre1 #pre2 #post1 #post2 #r:R.term)
                 (d_a: RT.tot_typing g a (RT.tm_type u))
                 (d_pre1: RT.tot_typing g pre1 tm_slprop)
                 (d_pre2: RT.tot_typing g pre2 tm_slprop)
                 (d_post1:RT.tot_typing g post1 (mk_arrow (a, R.Q_Explicit) tm_slprop))
                 (d_post2:RT.tot_typing g post2 (mk_arrow (a, R.Q_Explicit) tm_slprop))
                 (pre_equiv:RT.tot_typing g (`()) (stt_slprop_equiv pre1 pre2))
                 (post_equiv:RT.tot_typing g (`()) (stt_slprop_post_equiv u a post1 post2))
                 (d_r:RT.tot_typing g r (mk_stt_comp u a pre1 post1))
  : GTot (RT.tot_typing g (mk_sub_stt u a pre1 pre2 post1 post2 r) (mk_stt_comp u a pre2 post2))
  = admit()

let slprop_arrow (t:term) : term = tm_arrow (null_binder t) None (C_Tot tm_slprop)

#push-options "--fuel 2 --ifuel 1 --z3rlimit_factor 4"
let st_equiv_soundness_aux (g:stt_env)
                           (c0:ln_comp) (c1:ln_comp { comp_res c0 == comp_res c1 })
                           (d:st_equiv g c0 c1)
                           (r:R.term)
                           (d_r:RT.tot_typing (elab_env g) r (elab_comp c0)) 
  : GTot (RT.tot_typing (elab_env g) (elab_sub c0 c1 r) (elab_comp c1))
  = if C_ST? c0 && C_ST? c1 then
      let ST_SLPropEquiv _ _ _ x pre_typing res_typing post_typing _eq_res eq_pre eq_post = d in
      // assert (None? (lookup_ty g x));
      assert (None? (lookup g x));
      assume (~(x `Set.mem` RT.freevars (comp_post c0)));
      assume (~(x `Set.mem` RT.freevars (comp_post c1)));
      let open_term_spec (e:R.term) (x:var)
          : Lemma 
            (RT.open_term e x == RT.subst_term e (RT.open_with_var x 0))
            [SMTPat (RT.open_term e x)]
          = RT.open_term_spec e x
      in
      let pre_equiv = SLPropEquiv.slprop_equiv_unit_soundness pre_typing eq_pre in
      let g' = push_binding g x ppname_default (comp_res c0) in
      let post_equiv
        : RT.tot_typing (RT.extend_env (elab_env g) x (comp_res c0))
                    (`())
                    (stt_slprop_equiv 
                      (RT.open_term (comp_post c0) x)
                      (RT.open_term (comp_post c1) x))
          = SLPropEquiv.slprop_equiv_unit_soundness post_typing eq_post
      in
      let t0 = comp_res c0 in
      let r_res_typing = tot_typing_soundness res_typing in
      RT.close_open_inverse (comp_post c0) x;
      RT.close_open_inverse (comp_post c1) x;
      let d 
        : RT.tot_typing (elab_env g) _ 
                    (mk_arrow (t0, R.Q_Explicit)
                              (stt_slprop_equiv (comp_post c0)
                                               (comp_post c1)))
          = assume (stt_slprop_equiv (comp_post c0)
                                    (comp_post c1) ==
                    RT.subst_term
                      (stt_slprop_equiv
                        (RT.open_term (comp_post c0) x)
                        (RT.open_term (comp_post c1) x))
                      [ RT.ND x 0 ]);
            RT.T_Abs _ _ _ (`()) _ (comp_u c1) _ R.Q_Explicit _ r_res_typing post_equiv
      in
      let d = stt_slprop_equiv_abstract d in
      let abs_post0_typing
        : RT.tot_typing (elab_env g)
                        (elab_comp_post c0) // mk_abs t0 (elab_pure (comp_post c0)))
                        (slprop_arrow (comp_res c0))
        = mk_t_abs_tot _ _ res_typing post_typing
      in
      let abs_post1_typing
        : RT.tot_typing (elab_env g)
                        (elab_comp_post c1) //mk_abs t0 (elab_pure (comp_post c1)))
                        (slprop_arrow (comp_res c0))
        = mk_t_abs_tot _ _ res_typing (fst (slprop_equiv_typing eq_post) post_typing)
      in
      let (| pf, d |) =
        inst_intro_slprop_post_equiv r_res_typing abs_post0_typing abs_post1_typing d in
      let post_equiv =
        RT.T_PropIrrelevance _ _ _ _ _ d
          (RT.T_Sub _ _ _ _
            (stt_slprop_post_equiv_is_prop r_res_typing abs_post0_typing abs_post1_typing)
            (RT.Relc_total_ghost _ _))
      in
      inst_sub_stt #_ #(comp_u c1) r_res_typing 
                  (tot_typing_soundness pre_typing)
                  (tot_typing_soundness (fst (slprop_equiv_typing eq_pre) pre_typing))
                  abs_post0_typing
                  abs_post1_typing
                  pre_equiv
                  post_equiv
                  d_r
    else admit ()
#pop-options

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

let st_equiv_soundness (g:stt_env)
                       (c0 c1:ln_comp)
                       (d:st_equiv g c0 c1)
                       (r:R.term)
                       (d_r:RT.tot_typing (elab_env g) r (elab_comp c0)) 
  : GTot (RT.tot_typing (elab_env g) (elab_sub c0 c1 r) (elab_comp c1)) =

  if C_ST? c0 && C_ST? c1 then
    let ST_SLPropEquiv _ _ _ x pre_typing res_typing post_typing eq_res eq_pre eq_post = d in
    let c1' = with_st_comp c1 {(st_comp_of_comp c1) with res = comp_res c0} in
    assert (comp_post c1 == comp_post c1');
    let rpost1' =
      Pulse.Reflection.Util.mk_abs
        (comp_res c1') R.Q_Explicit (comp_post c1') in
    let rpost1 =
      Pulse.Reflection.Util.mk_abs
        (comp_res c1) R.Q_Explicit (comp_post c1) in
    
    // these two should follow, since we know x is not free in comp_post c1 and c2
    //   from the ST_SLPropEquiv rule
    assume (~ (x `Set.mem` (RT.freevars (comp_post c1))));
    assume (~ (x `Set.mem` (RT.freevars (comp_post c1'))));
    
    let d : RT.equiv (elab_env g) rpost1' rpost1 =
      RT.Rel_abs (elab_env g)
                 (comp_res c1')
                 (comp_res c1)
                 R.Q_Explicit
                 (comp_post c1')
                 (comp_post c1)
                 x
                 eq_res
                 (RT.Rel_refl _ _ _) in

    let d_eq : RT.equiv (elab_env g) (elab_comp c1') (elab_comp c1) =
      mk_stt_comp_equiv (elab_env g)
        (comp_u c1)
        (comp_res c1')
        (comp_pre c1')
        rpost1'
        (comp_res c1)
        (comp_pre c1)
        rpost1
        eq_res
        (RT.Rel_refl _ _ _)
        d
    in
    let d_steq : st_equiv g c0 c1' =
      ST_SLPropEquiv g c0 c1' x pre_typing res_typing post_typing (RT.Rel_refl _ _ _) eq_pre eq_post
    in
    let d : RT.tot_typing (elab_env g) (elab_sub c0 c1' r) (elab_comp c1') =
      st_equiv_soundness_aux g c0 c1' d_steq r d_r in
    assert (elab_sub c0 c1' r == elab_sub c0 c1 r);
    let d : RT.tot_typing (elab_env g) (elab_sub c0 c1 r) (elab_comp c1') =
      st_equiv_soundness_aux g c0 c1' d_steq r d_r in
    RT.T_Sub (elab_env g)
             (elab_sub c0 c1 r)
             (T.E_Total, elab_comp c1')
             (T.E_Total, elab_comp c1)
             d
             (RT.Relc_typ _ _ _ T.E_Total _ (RT.Rel_equiv _ _ _ _ d_eq))
  else admit ()
