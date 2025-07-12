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

module Pulse.Typing.Metatheory.Base
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing
module RU = Pulse.RuntimeUtils
module RT = FStar.Reflection.Typing

let admit_st_comp_typing (g:env) (st:st_comp) 
  : Dv (st_comp_typing g st)
  = admit(); 
    let x = fresh g in
    STC g st x (admit()) (admit()) (admit())

let admit_comp_typing (g:env) (c:comp_st)
  : Dv (comp_typing_u g c)
  = match c with
    | C_ST st ->
      CT_ST g st (admit_st_comp_typing g st)
    | C_STAtomic inames obs st ->
      CT_STAtomic g inames obs st (admit()) (admit_st_comp_typing g st)
    | C_STGhost inames st ->
      CT_STGhost g inames st (admit ()) (admit_st_comp_typing g st)      

let st_typing_correctness_ctot (#g:env) (#t:st_term) (#c:comp{C_Tot? c}) 
                               (_:st_typing g t c)
: (u:Ghost.erased universe & universe_of g (comp_res c) u)
= let u : Ghost.erased universe = RU.magic () in
  let ty : universe_of g (comp_res c) u = RU.magic() in
  (| u, ty |)    

let st_typing_correctness (#g:env) (#t:st_term) (#c:comp_st) 
                          (_:st_typing g t c)
  : Dv (comp_typing_u g c)
  = admit_comp_typing g c
    
let add_frame_well_typed (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
                         (#f:term) (ft:tot_typing g f tm_slprop)
  : Dv (comp_typing_u g (add_frame c f))
  = admit_comp_typing _ _

let emp_inames_typing (g:env) : tot_typing g tm_emp_inames tm_inames = RU.magic()

let comp_typing_inversion #g #c ct = 
  match ct with
  | CT_ST _ _ st -> st, emp_inames_typing g
  | CT_STGhost _ _ _ it st
  | CT_STAtomic _ _ _ _ it st -> st, it

let st_comp_typing_inversion_cofinite (#g:env) (#st:_) (ct:st_comp_typing g st) = 
  admit(), admit(), (fun _ -> admit())

let st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st) = 
  let STC g st x ty pre post = ct in
  (| ty, pre, x, post |)

let tm_exists_inversion (#g:env) (#u:universe) (#ty:term) (#p:term) 
                        (_:tot_typing g (tm_exists_sl u (as_binder ty) p) tm_slprop)
                        (x:var { fresh_wrt x g (freevars p) } )
  : universe_of g ty u &
    tot_typing (push_binding g x ppname_default ty) p tm_slprop
  = admit(), admit()

let pure_typing_inversion (#g:env) (#p:term) (_:tot_typing g (tm_pure p) tm_slprop)
   : tot_typing g p (wr FStar.Reflection.Typing.tm_prop Range.range_0)
   = admit ()

let typing_correctness _ = admit()
let tot_typing_renaming1 _ _ _ _ _ _ = admit()
let tot_typing_weakening _ _ _ _ _ _ = admit ()

let non_informative_t_weakening (g g':env) (g1:env{ pairwise_disjoint g g1 g' })
  (u:universe) (t:term)
  (d:non_informative_t (push_env g g') u t)
  : non_informative_t (push_env (push_env g g1) g') u t =
  let (| w, _ |) = d in
  (| w, RU.magic #(tot_typing _ _ _) () |)

let non_informative_c_weakening (g g':env) (g1:env{ pairwise_disjoint g g1 g' })
  (c:comp_st)
  (d:non_informative_c (push_env g g') c)
  : non_informative_c (push_env (push_env g g1) g') c =
  non_informative_t_weakening g g' g1 _ _ d

let bind_comp_weakening (g:env) (g':env { disjoint g g' })
  (#x:var) (#c1 #c2 #c3:comp) (d:bind_comp (push_env g g') x c1 c2 c3)
  (g1:env { pairwise_disjoint g g1 g' })
  : Dv (bind_comp (push_env (push_env g g1) g') x c1 c2 c3)
        (decreases d) =
  
  match d with
  | Bind_comp _ x c1 c2 _ _ _ ->
    assume (None? (lookup (push_env g g1) x));
    let y = fresh (push_env (push_env g g1) g') in
    assume (~ (y `Set.mem` (freevars (comp_post c2))));
    Bind_comp _ x c1 c2 (RU.magic ()) y (RU.magic ())

let lift_comp_weakening (g:env) (g':env { disjoint g g'})
  (#c1 #c2:comp) (d:lift_comp (push_env g g') c1 c2)
  (g1:env { pairwise_disjoint g g1 g' })
  : Tot (lift_comp (push_env (push_env g g1) g') c1 c2)
        (decreases d) =
  
  match d with
  | Lift_STAtomic_ST _ c -> Lift_STAtomic_ST _ c
  | Lift_Ghost_Neutral _ c non_informative_c ->
    Lift_Ghost_Neutral _ c (non_informative_c_weakening g g' g1 _ non_informative_c)
  | Lift_Neutral_Ghost _ c -> Lift_Neutral_Ghost _ c
  | Lift_Observability _ obs c -> Lift_Observability _ obs c

// TODO: the proof for RT.Equiv is not correct here
let equiv_weakening (g:env) (g':env { disjoint g g' })
  #t1 #t2 (d:RT.equiv (elab_env (push_env g g')) t1 t2)
  (g1:env { pairwise_disjoint g g1 g' })
  : RT.equiv (elab_env (push_env (push_env g g1) g')) t1 t2 =
  admit ();
  d

let st_equiv_weakening (g:env) (g':env { disjoint g g' })
  (#c1 #c2:comp) (d:st_equiv (push_env g g') c1 c2)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_equiv (push_env (push_env g g1) g') c1 c2 =
  match d with
  | ST_SLPropEquiv _ c1 c2 x _ _ _ hequiv _ _ ->
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    ST_SLPropEquiv _ c1 c2 x (RU.magic ()) (RU.magic ()) (RU.magic ())
      (equiv_weakening _ _ hequiv _) (RU.magic ()) (RU.magic ())
  | ST_TotEquiv _ t1 t2 u _ _ ->
    ST_TotEquiv _ t1 t2 u (RU.magic ()) (RU.magic ())

// TODO: add precondition that g1 extends g'
let prop_validity_token_weakening (#g:env) (#t:term)
  (token:prop_validity g t)
  (g1:env)
  : prop_validity g1 t =
  admit ();
  token

let rec st_sub_weakening (g:env) (g':env { disjoint g g' })
  (#c1 #c2:comp) (d:st_sub (push_env g g') c1 c2)
  (g1:env { pairwise_disjoint g g1 g' })
  : Tot (st_sub (push_env (push_env g g1) g') c1 c2)
        (decreases d)
=
  let g'' = push_env (push_env g g1) g' in
  match d with
  | STS_Refl _ _ ->
    STS_Refl _ _
  | STS_Trans _ _ _ _ dl dr ->
    STS_Trans _ _ _ _ (st_sub_weakening g g' dl g1) (st_sub_weakening g g' dr g1)
  | STS_GhostInvs _ stc is1 is2 tok ->
    let tok : prop_validity g'' (tm_inames_subset is1 is2) = prop_validity_token_weakening tok g'' in
    STS_GhostInvs g'' stc is1 is2 tok
  | STS_AtomicInvs _ stc is1 is2 o1 o2 tok ->
    let tok : prop_validity g'' (tm_inames_subset is1 is2) = prop_validity_token_weakening tok g'' in
    STS_AtomicInvs g'' stc is1 is2 o1 o2 tok

let st_comp_typing_weakening (g:env) (g':env { disjoint g g' })
  (#s:st_comp) (d:st_comp_typing (push_env g g') s)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_comp_typing (push_env (push_env g g1) g') s =
  match d with
  | STC _ st x _ _ _ ->
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    STC _ st x (RU.magic ()) (RU.magic ()) (RU.magic ())

let comp_typing_weakening (g:env) (g':env { disjoint g g' })
  (#c:comp) (#u:universe) (d:comp_typing (push_env g g') c u)
  (g1:env { pairwise_disjoint g g1 g' })
  : comp_typing (push_env (push_env g g1) g') c u =
  match d with
  | CT_Tot _ t u _ -> CT_Tot _ t u (RU.magic ())
  | CT_ST _ _ d -> CT_ST _ _ (st_comp_typing_weakening g g' d g1)
  | CT_STAtomic _ inames obs _ _ d ->
    CT_STAtomic _ inames obs _ (RU.magic ()) (st_comp_typing_weakening g g' d g1)
  | CT_STGhost _ inames _ _ d ->
    CT_STGhost _ inames _ (RU.magic ()) (st_comp_typing_weakening g g' d g1)

#push-options "--split_queries no --z3rlimit_factor 4 --fuel 1 --ifuel 1"
let rec st_typing_weakening g g' t c d g1
  : Dv (st_typing (push_env (push_env g g1) g') t c)
        (decreases d) =
  
  match d with
  | T_Abs g x q b u body c b_typing body_typing ->
    FStar.Pure.BreakVC.break_vc();
    // T_Abs is used only at the top, should not come up
    assume false;
    let x = fresh (push_env (push_env g g1) g') in
    T_Abs g x q b u body c (RU.magic #(tot_typing _ _ _) ()) 
                          (st_typing_weakening g g' body c body_typing g1)
  | T_STApp _ head ty q res arg _ _ ->
    FStar.Pure.BreakVC.break_vc();
    T_STApp _ head ty q res arg (RU.magic #(tot_typing _ _ _) ()) (RU.magic #(tot_typing _ _ _) ())

  | T_STGhostApp _ head ty q res arg _ _ _ _ ->
    FStar.Pure.BreakVC.break_vc();
    // candidate for renaming
    let x = fresh (push_env (push_env g g1) g') in
    assume (~ (x `Set.mem` freevars_comp res));
    T_STGhostApp _ head ty q res arg x (RU.magic ()) (RU.magic ()) (RU.magic ())

  | T_Return _ c use_eq u t e post x_old _ _ _ ->
    FStar.Pure.BreakVC.break_vc();
    let x = fresh (push_env (push_env g g1) g') in
    assume (~ (x `Set.mem` freevars post));
    // x is only used to open and then close
    assume (comp_return c use_eq u t e post x_old ==
            comp_return c use_eq u t e post x);
    T_Return _ c use_eq u t e post x (RU.magic ()) (RU.magic ()) (RU.magic ())

  | T_Lift _ e c1 c2 d_c1 d_lift ->
    FStar.Pure.BreakVC.break_vc();
    T_Lift _ e c1 c2 (st_typing_weakening g g' e c1 d_c1 g1)
                     (lift_comp_weakening g g' d_lift g1)

  | T_Bind _ e1 e2 c1 c2 b x c d_e1 _ d_e2 d_bc ->
    FStar.Pure.BreakVC.break_vc();
    let d_e1 : st_typing (push_env (push_env g g1) g') e1 c1 =
      st_typing_weakening g g' e1 c1 d_e1 g1 in
    //
    // When we call it, g' will actually be empty
    // And they way bind checker invokes the lemma, we also know x is not in g1
    // But we must fix it cleanly
    // Perhaps typing rules should take a thunk, fun (x:var) ...
    //
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    let d_e2
      : st_typing (push_binding (push_env g g') x ppname_default (comp_res c1))
                  (open_st_term_nv e2 (b.binder_ppname, x))
                  c2 = d_e2 in
    assert (equal (push_binding (push_env g g') x ppname_default (comp_res c1))
                  (push_env g (push_binding g' x ppname_default (comp_res c1))));
    let d_e2
      : st_typing (push_env g (push_binding g' x ppname_default (comp_res c1)))
                  (open_st_term_nv e2 (b.binder_ppname, x))
                  c2 = d_e2 in
    let d_e2
      : st_typing (push_env (push_env g g1) (push_binding g' x ppname_default (comp_res c1)))
                  (open_st_term_nv e2 (b.binder_ppname, x))
                  c2 = st_typing_weakening g (push_binding g' x ppname_default (comp_res c1)) _ _ d_e2 g1 in
    assert (equal (push_env (push_env g g1) (push_binding g' x ppname_default (comp_res c1)))
                  (push_binding (push_env (push_env g g1) g') x ppname_default (comp_res c1)));
    let d_e2
      : st_typing (push_binding (push_env (push_env g g1) g') x ppname_default (comp_res c1))
                  (open_st_term_nv e2 (b.binder_ppname, x))
                  c2 = d_e2 in
    let d_bc = bind_comp_weakening g g' d_bc g1 in
    T_Bind _ e1 e2 c1 c2 b x c d_e1 (RU.magic ()) d_e2 d_bc

  | T_BindFn _ e1 e2 c1 c2 b x d_e1 u _ d_e2 c2_typing  ->
    FStar.Pure.BreakVC.break_vc();
    let d_e1 : st_typing (push_env (push_env g g1) g') e1 c1 =
      st_typing_weakening g g' e1 c1 d_e1 g1 in
    //
    // When we call it, g' will actually be empty
    // And they way bind checker invokes the lemma, we also know x is not in g1
    // But we must fix it cleanly
    // Perhaps typing rules should take a thunk, fun (x:var) ...
    //
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    let d_e2
      : st_typing (push_binding (push_env g g') x ppname_default (comp_res c1))
                  (open_st_term_nv e2 (b.binder_ppname, x))
                  c2 = d_e2 in
    assert (equal (push_binding (push_env g g') x ppname_default (comp_res c1))
                  (push_env g (push_binding g' x ppname_default (comp_res c1))));
    let d_e2
      : st_typing (push_env g (push_binding g' x ppname_default (comp_res c1)))
                  (open_st_term_nv e2 (b.binder_ppname, x))
                  c2 = d_e2 in
    let d_e2
      : st_typing (push_env (push_env g g1) (push_binding g' x ppname_default (comp_res c1)))
                  (open_st_term_nv e2 (b.binder_ppname, x))
                  c2 = st_typing_weakening g (push_binding g' x ppname_default (comp_res c1)) _ _ d_e2 g1 in
    assert (equal (push_env (push_env g g1) (push_binding g' x ppname_default (comp_res c1)))
                  (push_binding (push_env (push_env g g1) g') x ppname_default (comp_res c1)));
    let d_e2
      : st_typing (push_binding (push_env (push_env g g1) g') x ppname_default (comp_res c1))
                  (open_st_term_nv e2 (b.binder_ppname, x))
                  c2 = d_e2 in
    let c2_typing = comp_typing_weakening g g' c2_typing g1 in
    T_BindFn _ e1 e2 c1 c2 b x d_e1 u (RU.magic #(tot_typing _ _ _) ()) d_e2 c2_typing

  | T_If _ b e1 e2 c hyp _ d_e1 d_e2 _ ->
    FStar.Pure.BreakVC.break_vc();
    assume (~ (hyp `Set.mem` dom g'));
    assume (~ (hyp `Set.mem` dom g1));
    let d_e1
      : st_typing (push_binding (push_env g g') hyp ppname_default (mk_eq2 u0 tm_bool b tm_true))
        e1 c = d_e1 in
    assert (equal (push_binding (push_env g g') hyp ppname_default (mk_eq2 u0 tm_bool b tm_true))
                  (push_env g (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_true))));
    let d_e1
      : st_typing (push_env g (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_true)))
                  e1 c = d_e1 in
    let d_e1
      : st_typing (push_env (push_env g g1) (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_true)))
                  e1 c = st_typing_weakening g (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_true)) _ _ d_e1 g1 in
    assert (equal (push_env (push_env g g1) (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_true)))
                  (push_binding (push_env (push_env g g1) g') hyp ppname_default (mk_eq2 u0 tm_bool b tm_true))); 
    let d_e1
      : st_typing (push_binding (push_env (push_env g g1) g') hyp ppname_default (mk_eq2 u0 tm_bool b tm_true))
                  e1 c = d_e1 in
    let d_e2
      : st_typing (push_binding (push_env g g') hyp ppname_default (mk_eq2 u0 tm_bool b tm_false))
                  e2 c = d_e2 in
    assert (equal (push_binding (push_env g g') hyp ppname_default (mk_eq2 u0 tm_bool b tm_false))
                  (push_env g (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_false))));
    let d_e2
      : st_typing (push_env g (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_false)))
                  e2 c = d_e2 in
    let d_e2
      : st_typing (push_env (push_env g g1) (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_false)))
                  e2 c = st_typing_weakening g (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_false)) _ _ d_e2 g1 in
    assert (equal (push_env (push_env g g1) (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_false)))
                  (push_binding (push_env (push_env g g1) g') hyp ppname_default (mk_eq2 u0 tm_bool b tm_false))); 
    let d_e2
      : st_typing (push_binding (push_env (push_env g g1) g') hyp ppname_default (mk_eq2 u0 tm_bool b tm_false))
                  e2 c = d_e2 in

    T_If _ b e1 e2 c hyp (RU.magic ()) d_e1 d_e2 (RU.magic ())
  
  | T_Match _ sc_u sc_ty sc d_sc_ty d_sc c c_typing brs d_brs d_pats_complete ->
    FStar.Pure.BreakVC.break_vc();
    admit();
    T_Match (push_env (push_env g g1) g')
            sc_u sc_ty sc
            (tot_typing_weakening g g' _ _ d_sc_ty g1)
            (tot_typing_weakening g g' _ _ d_sc g1)
            c c_typing 
            brs d_brs
            d_pats_complete

  | T_Frame _ e c frame _ d_e ->
    FStar.Pure.BreakVC.break_vc();
    T_Frame _ e c frame (RU.magic ()) (st_typing_weakening g g' e c d_e g1)

  | T_Equiv _ e c c' d_e d_eq ->
    FStar.Pure.BreakVC.break_vc();
    T_Equiv _ e c c' (st_typing_weakening g g' e c d_e g1) (st_equiv_weakening g g' d_eq g1)

  | T_Sub _ e c c' d_e d_sub ->
    FStar.Pure.BreakVC.break_vc();
    T_Sub _ e c c' (st_typing_weakening g g' e c d_e g1) (st_sub_weakening g g' d_sub g1)

  | T_IntroPure _ p _ token ->
    FStar.Pure.BreakVC.break_vc();
    T_IntroPure _ p (RU.magic ()) (prop_validity_token_weakening token _)

  | T_ElimExists _ u t p x _ _ ->
    FStar.Pure.BreakVC.break_vc();
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    T_ElimExists _ u t p x (RU.magic ()) (RU.magic ())

  | T_IntroExists _ u b p e _ _ _ ->
    FStar.Pure.BreakVC.break_vc();
    T_IntroExists _ u b p e (RU.magic ()) (RU.magic ()) (RU.magic ())

  | T_While _ inv cond body _ cond_typing body_typing ->
    FStar.Pure.BreakVC.break_vc();
    T_While _ inv cond body (RU.magic ())
      (st_typing_weakening g g' cond (comp_while_cond ppname_default inv) cond_typing g1)
      (st_typing_weakening g g' body (comp_while_body ppname_default inv) body_typing g1)

  | T_Par _ eL cL eR cR x cL_typing cR_typing eL_typing eR_typing ->
    FStar.Pure.BreakVC.break_vc();
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    T_Par _ eL cL eR cR x
      (comp_typing_weakening g g' cL_typing g1)
      (comp_typing_weakening g g' cR_typing g1)
      (st_typing_weakening g g' eL cL eL_typing g1)
      (st_typing_weakening g g' eR cR eR_typing g1)

  | T_WithLocal _ ppname init body init_t c x _ _ d_c d_body ->
    FStar.Pure.BreakVC.break_vc();
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    let d_body
      : st_typing (push_binding (push_env g g') x ppname_default (mk_ref init_t))
                  (open_st_term_nv body (v_as_nv x))
                  (comp_withlocal_body x init_t init c) = d_body in
    assert (equal (push_binding (push_env g g') x ppname_default (mk_ref init_t))
                  (push_env g (push_binding g' x ppname_default (mk_ref init_t))));
    let d_body
      : st_typing (push_env g (push_binding g' x ppname_default (mk_ref init_t)))
                  (open_st_term_nv body (v_as_nv x))
                  (comp_withlocal_body x init_t init c) = d_body in
    let d_body
      : st_typing (push_env (push_env g g1) (push_binding g' x ppname_default (mk_ref init_t)))
                  (open_st_term_nv body (v_as_nv x))
                  (comp_withlocal_body x init_t init c)
      = st_typing_weakening g (push_binding g' x ppname_default (mk_ref init_t))  _ _ d_body g1 in
    assert (equal (push_env (push_env g g1) (push_binding g' x ppname_default (mk_ref init_t)))
                  (push_binding (push_env (push_env g g1) g') x ppname_default (mk_ref init_t)));
    let d_body
      : st_typing (push_binding (push_env (push_env g g1) g') x ppname_default (mk_ref init_t))
                  (open_st_term_nv body (v_as_nv x))
                  (comp_withlocal_body x init_t init c) = d_body in
    T_WithLocal _ ppname init body init_t c x (RU.magic ()) (RU.magic ())
      (comp_typing_weakening g g' d_c g1)
      d_body

  | T_WithLocalArray _ ppname init len body init_t c x _ _ _ d_c d_body ->
    FStar.Pure.BreakVC.break_vc();
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    let d_body
      : st_typing (push_binding (push_env g g') x ppname_default (mk_array init_t))
                  (open_st_term_nv body (v_as_nv x))
                  (comp_withlocal_array_body x init_t init len c) = d_body in
    assert (equal (push_binding (push_env g g') x ppname_default (mk_array init_t))
                  (push_env g (push_binding g' x ppname_default (mk_array init_t))));
    let d_body
      : st_typing (push_env g (push_binding g' x ppname_default (mk_array init_t)))
                  (open_st_term_nv body (v_as_nv x))
                  (comp_withlocal_array_body x init_t init len c) = d_body in
    let d_body
      : st_typing (push_env (push_env g g1) (push_binding g' x ppname_default (mk_array init_t)))
                  (open_st_term_nv body (v_as_nv x))
                  (comp_withlocal_array_body x init_t init len c)
      = st_typing_weakening g (push_binding g' x ppname_default (mk_array init_t))  _ _ d_body g1 in
    assert (equal (push_env (push_env g g1) (push_binding g' x ppname_default (mk_array init_t)))
                  (push_binding (push_env (push_env g g1) g') x ppname_default (mk_array init_t)));
    let d_body
      : st_typing (push_binding (push_env (push_env g g1) g') x ppname_default (mk_array init_t))
                  (open_st_term_nv body (v_as_nv x))
                  (comp_withlocal_array_body x init_t init len c) = d_body in
    T_WithLocalArray _ ppname init len body init_t c x (RU.magic ()) (RU.magic ()) (RU.magic ())
      (comp_typing_weakening g g' d_c g1)
      d_body

  | T_Rewrite _ p q _ _ ->
    FStar.Pure.BreakVC.break_vc();
    T_Rewrite _ p q (RU.magic ()) (RU.magic ())

  | T_Admit _ c d_c ->
    FStar.Pure.BreakVC.break_vc();
    T_Admit _ c (comp_typing_weakening g g' d_c g1)

  | T_Unreachable _ c d_c tok ->
    FStar.Pure.BreakVC.break_vc();
    T_Unreachable _ c (comp_typing_weakening g g' d_c g1) (RU.magic ())  // weaken tok

  | T_WithInv  _ _ _ _ _ i_typing p_typing body_typing tok ->
    FStar.Pure.BreakVC.break_vc();
    T_WithInv _ _ _ _ _ (tot_typing_weakening g g' _ _ i_typing g1)
                        (tot_typing_weakening g g' _ _ p_typing g1)
                        (st_typing_weakening g g' _ _ body_typing g1)
                        (prop_validity_token_weakening tok _)
#pop-options

let non_informative_t_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (u:universe) (t1:term)
  (d:non_informative_t (push_env g (push_env (singleton_env (fstar_env g) x t) g')) u t1)

  : non_informative_t (push_env g (subst_env g' (nt x e))) u (subst_term t1 (nt x e)) =

  let ss = nt x e in

  let (| w, _ |) = d in
  (| subst_term w ss, RU.magic #(tot_typing _ _ _) () |)

let non_informative_c_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (c:comp_st)
  (d:non_informative_c (push_env g (push_env (singleton_env (fstar_env g) x t) g')) c)

  : non_informative_c (push_env g (subst_env g' (nt x e))) (subst_comp c (nt x e)) =

  non_informative_t_subst g x t g' e_typing _ _ d

let lift_comp_subst
  (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#c1 #c2:comp)
  (d:lift_comp (push_env g (push_env (singleton_env (fstar_env g) x t) g')) c1 c2)

  : lift_comp (push_env g (subst_env g' (nt x e)))
              (subst_comp c1 (nt x e))
              (subst_comp c2 (nt x e)) =

  let ss = nt x e in
  
  match d with
  | Lift_STAtomic_ST _ c ->
    Lift_STAtomic_ST _ (subst_comp c ss)

  | Lift_Ghost_Neutral _ c d_non_informative ->
    Lift_Ghost_Neutral _ (subst_comp c ss)
      (non_informative_c_subst g x t g' e_typing _ d_non_informative)
  
  | Lift_Neutral_Ghost _ c ->
    Lift_Neutral_Ghost _ (subst_comp c ss)
  
  | Lift_Observability _ c o ->
    Lift_Observability _ (subst_comp c ss) o

let bind_comp_subst
  (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#y:var) (#c1 #c2 #c3:comp_st) (d:bind_comp (push_env g (push_env (singleton_env (fstar_env g) x t) g')) y c1 c2 c3)
  : bind_comp (push_env g (subst_env g' (nt x e)))
              y
              (subst_comp c1 (nt x e))
              (subst_comp c2 (nt x e))
              (subst_comp c3 (nt x e)) =
  
  let ss = nt x e in

  match d with
  | Bind_comp _ y c1 c2 _ z _ ->
    assume bind_comp_pre y (S.subst_comp c1 ss) (S.subst_comp c2 ss);
    assume None? (lookup (push_env g (subst_env g' (nt x e))) z) /\
        ~(Set.mem z (S.freevars (S.comp_post (S.subst_comp c2 ss))));
    Bind_comp _ y (subst_comp c1 ss)
                  (subst_comp c2 ss)
                  (RU.magic ())
                  z
                  (RU.magic ())


let st_equiv_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#c1 #c2:comp) (d:st_equiv (push_env g (push_env (singleton_env (fstar_env g) x t) g')) c1 c2)
  : st_equiv (push_env g (subst_env g' (nt x e)))
             (subst_comp c1 (nt x e))
             (subst_comp c2 (nt x e)) =
  match d with
  | ST_SLPropEquiv _ c1 c2 y _ _ _ hequiv _ _ ->
    assume None? (lookup (push_env g (subst_env g' (nt x e))) y) /\
        ~(Set.mem y (S.freevars (S.comp_post (S.subst_comp c1 (nt x e))))) /\
        ~(Set.mem y (S.freevars (S.comp_post (S.subst_comp c2 (nt x e)))));
    ST_SLPropEquiv _ (subst_comp c1 (nt x e))
                    (subst_comp c2 (nt x e))
                    y
                    (RU.magic ())
                    (RU.magic ())
                    (RU.magic ())
                    (admit (); hequiv)  // TODO: incorrect proof
                    (RU.magic ())
                    (RU.magic ())
  | ST_TotEquiv _ t1 t2 u _ _ ->
    ST_TotEquiv _ (subst_term t1 (nt x e)) (subst_term t2 (nt x e)) u (RU.magic ()) (RU.magic ())

let st_comp_typing_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#s:st_comp) (d:st_comp_typing (push_env g (push_env (singleton_env (fstar_env g) x t) g')) s)
  : st_comp_typing (push_env g (subst_env g' (nt x e)))
                   (subst_st_comp s (nt x e)) =
  match d with
  | STC _ s y _ _ _ ->
    assume None? (lookup (push_env g (subst_env g' (nt x e))) y) /\
        ~(Set.mem y (S.freevars (S.subst_st_comp s (nt x e)).post));
    STC _ (subst_st_comp s (nt x e))
         y
         (RU.magic ())
         (RU.magic ())
         (RU.magic ())

let comp_typing_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#c:comp) (#u:universe) (d:comp_typing (push_env g (push_env (singleton_env (fstar_env g) x t) g')) c u)
  : comp_typing (push_env g (subst_env g' (nt x e)))
                (subst_comp c (nt x e)) u =
  match d with
  | CT_Tot _ t u _ ->
    CT_Tot _ (subst_term t (nt x e)) u (RU.magic ())
  | CT_ST _ s d_s ->
    CT_ST _ (subst_st_comp s (nt x e)) (st_comp_typing_subst g x t g' e_typing d_s)
  | CT_STAtomic _ inames obs s _ d_s ->
    CT_STAtomic _ (subst_term inames (nt x e)) obs (subst_st_comp s (nt x e)) (RU.magic ()) (st_comp_typing_subst g x t g' e_typing d_s)
  | CT_STGhost _ inames s _ d_s ->
    CT_STGhost _ (subst_term inames (nt x e)) (subst_st_comp s (nt x e)) (RU.magic ()) (st_comp_typing_subst g x t g' e_typing d_s)
  

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b { y == x } = x

let rec st_typing_subst g x t g' #e #eff e_typing #e1 #c1 e1_typing _
  : Tot (st_typing (push_env g (subst_env g' (nt x e)))
                   (subst_st_term e1 (nt x e))
                   (subst_comp c1 (nt x e)))
        (decreases e1_typing) =
  
  let ss = nt x e in

  match e1_typing with
  | T_Abs .. ->
    Pervasives.coerce_eq (RU.magic ()) e1_typing

  | T_STApp _ head ty q res arg _ _ ->
    admit ();
    T_STApp _ (subst_term head ss)
              (subst_term ty ss)
              q
              (subst_comp res ss)
              (subst_term arg ss)
              (RU.magic ())
              (RU.magic ())

 | T_STGhostApp _ head ty q res arg x _ _ _ ->
    admit ();
    T_STGhostApp _ (subst_term head ss)
              (subst_term ty ss)
              q
              (subst_comp res ss)
              (subst_term arg ss)
              x
              (RU.magic ())
              (RU.magic ())
              (RU.magic ())

  | T_Return _ c use_eq u t e post x _ _ _ ->
    admit ();
    T_Return _ c use_eq u
      (subst_term t ss)
      (subst_term e ss)
      (subst_term post ss)
      x
      (RU.magic ())
      (RU.magic ())
      (RU.magic ())

  | T_Lift _ e c1 c2 d_e d_lift ->
    admit ();
    T_Lift _ (subst_st_term e ss)
             (subst_comp c1 ss)
             (subst_comp c2 ss)
             (st_typing_subst g x t g' e_typing d_e (RU.magic ()))
             (lift_comp_subst g x t g' e_typing d_lift)

  | T_Bind _ e1 e2 c1 c2 b y c d_e1 _ d_e2 d_bc ->
    admit ();
    T_Bind _ (subst_st_term e1 ss)
             (subst_st_term e2 ss)
             (subst_comp c1 ss)
             (subst_comp c2 ss)
             (subst_binder b ss)
             y
             (subst_comp c ss)
             (st_typing_subst g x t g' e_typing d_e1 (RU.magic ()))
             (RU.magic ())
             (coerce_eq (st_typing_subst g x t (push_binding g' y ppname_default (comp_res c1)) e_typing d_e2 (RU.magic ())) ())
             (bind_comp_subst g x t g' e_typing d_bc)

  | T_BindFn _ e1 e2 c1 c2 b y d_e1 u _ d_e2 d_c2 ->
    admit ();
    T_BindFn _ (subst_st_term e1 ss)
               (subst_st_term e2 ss)
               (subst_comp c1 ss)
               (subst_comp c2 ss)
               (subst_binder b ss)
               y
               (st_typing_subst g x t g' e_typing d_e1 (RU.magic ()))
               u
               (RU.magic ())
               (coerce_eq (st_typing_subst g x t (push_binding g' y ppname_default (comp_res c1)) e_typing d_e2 (RU.magic ())) ())
               (comp_typing_subst g x t (push_binding g' y ppname_default (comp_res c1)) e_typing d_c2)
 
  | T_If _ b e1 e2 c hyp _ d_e1 d_e2 _ ->
    admit ();
    T_If _ (subst_term b ss)
           (subst_st_term e1 ss)
           (subst_st_term e2 ss)
           (subst_comp c ss)
           hyp
           (RU.magic ())
           (coerce_eq (st_typing_subst g x t (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_true)) e_typing d_e1 (RU.magic ())) ())
           (coerce_eq (st_typing_subst g x t (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_false)) e_typing d_e2 (RU.magic ())) ())
           (RU.magic ())

  | T_Match _ sc_u sc_ty sc _ty_typing _sc_typing c c_typing brs brs_typing pats_complete ->
    Pervasives.coerce_eq (RU.magic ()) e1_typing

  | T_Frame _ e c frame _ d_e ->
    admit ();
    T_Frame _ (subst_st_term e ss)
              (subst_comp c ss)
              (subst_term frame ss)
              (RU.magic ())
              (st_typing_subst g x t g' e_typing d_e (RU.magic ()))

  | T_Equiv _ e c c' d_e d_eq ->
    admit ();
    T_Equiv _ (subst_st_term e ss)
              (subst_comp c ss)
              (subst_comp c' ss)
              (st_typing_subst g x t g' e_typing d_e (RU.magic ()))
              (st_equiv_subst g x t g' e_typing d_eq)
  
  | T_Sub _ e c c' d_e d_eq ->
    admit ();
    T_Sub _ (subst_st_term e ss)
            (subst_comp c ss)
            (subst_comp c' ss)
            (st_typing_subst g x t g' e_typing d_e (RU.magic ()))
            (coerce_eq d_eq ())

  | T_IntroPure _ p _ _ ->
    admit ();
    T_IntroPure _ (subst_term p ss)
                  (RU.magic ())
                  (RU.magic ())

  | T_ElimExists _ u t p y _ _ ->
    admit ();
    T_ElimExists _ u (subst_term t ss) (subst_term p ss) y (RU.magic ()) (RU.magic ())

  | T_IntroExists _ u b p e _ _ _ ->
    admit ();
    T_IntroExists _ u (subst_binder b ss)
                      (subst_term p ss)
                      (subst_term e ss)
                      (RU.magic ())
                      (RU.magic ())
                      (RU.magic ())

  | T_While _ inv cond body _ cond_typing body_typing ->
    admit ();
    T_While _ (subst_term inv ss)
              (subst_st_term cond ss)
              (subst_st_term body ss)
              (RU.magic ())
              (st_typing_subst g x t g' e_typing cond_typing (RU.magic ()))
              (st_typing_subst g x t g' e_typing body_typing (RU.magic ()))

  | T_Par _ eL cL eR cR y d_cL d_cR d_eL d_eR ->
    admit ();
    T_Par _ (subst_st_term eL ss)
            (subst_comp cL ss)
            (subst_st_term eR ss)
            (subst_comp cR ss)
            y
            (comp_typing_subst g x t g' e_typing d_cL)
            (comp_typing_subst g x t g' e_typing d_cR)
            (st_typing_subst g x t g' e_typing d_eL (RU.magic ()))
            (st_typing_subst g x t g' e_typing d_eR (RU.magic ()))

  | T_WithLocal _ ppname init body init_t c y _ _ d_c d_body ->
    admit ();
    T_WithLocal _ ppname
                  (subst_term init ss)
                  (subst_st_term body ss)
                  (subst_term init_t ss)
                  (subst_comp c ss)
                  y
                  (RU.magic ())
                  (RU.magic ())
                  (comp_typing_subst g x t g' e_typing d_c)
                  (coerce_eq (st_typing_subst g x t (push_binding g' y ppname_default (mk_ref init_t)) e_typing d_body (RU.magic ())) ())

  | T_WithLocalArray _ ppname init len body init_t c y _ _ _ d_c d_body ->
    admit ();
    T_WithLocalArray _ ppname
                       (subst_term init ss)
                       (subst_term len ss)
                       (subst_st_term body ss)
                       (subst_term init_t ss)
                       (subst_comp c ss)
                       y
                       (RU.magic ())
                       (RU.magic ())
                       (RU.magic ())
                       (comp_typing_subst g x t g' e_typing d_c)
                       (coerce_eq (st_typing_subst g x t (push_binding g' y ppname_default (mk_ref init_t)) e_typing d_body (RU.magic ())) ())

  | T_Rewrite _ p q _ _ ->
    admit ();
    T_Rewrite _ (subst_term p ss)
                (subst_term q ss)
                (RU.magic ())
                (RU.magic ())

  | T_Admit _ c d_c ->
    admit ();
    T_Admit _ (subst_comp c ss) (comp_typing_subst g x t g' e_typing d_c)

  | T_Unreachable _ c d_c d_p ->
    admit ();
    T_Unreachable _ (subst_comp c ss) (comp_typing_subst g x t g' e_typing d_c) (coerce_eq d_p ())
  
  | T_WithInv _ i p body c d_i d_p d_body d_tok ->
    admit ();
    T_WithInv _ (subst_term i ss) (subst_term p ss) (subst_st_term body ss) (subst_comp c ss)
      (RU.magic ()) (RU.magic ()) (st_typing_subst g x t g' e_typing d_body _) (RU.magic ())
