module Pulse.Typing.Metatheory
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

let admit_st_comp_typing (g:env) (st:st_comp) 
  : st_comp_typing g st
  = admit(); 
    STC g st (fresh g) (admit()) (admit()) (admit())

let admit_comp_typing (g:env) (c:comp_st)
  : comp_typing_u g c
  = match c with
    | C_ST st ->
      CT_ST g st (admit_st_comp_typing g st)
    | C_STAtomic inames st ->
      CT_STAtomic g inames st (admit()) (admit_st_comp_typing g st)
    | C_STGhost inames st ->
      CT_STGhost g inames st (admit()) (admit_st_comp_typing g st)      

let st_typing_correctness (#g:env) (#t:st_term) (#c:comp_st) 
                          (_:st_typing g t c)
  : comp_typing_u g c
  = admit_comp_typing g c
    
let add_frame_well_typed (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
                         (#f:term) (ft:tot_typing g f tm_vprop)
  : comp_typing_u g (add_frame c f)
  = admit_comp_typing _ _

let comp_typing_inversion #g #c ct = 
  match ct with
  | CT_ST _ _ st
  | CT_STAtomic _ _ _ _ st 
  | CT_STGhost _ _ _ _ st   -> st

let st_comp_typing_inversion_cofinite (#g:env) (#st:_) (ct:st_comp_typing g st) = 
  admit(), admit(), (fun _ -> admit())

let st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st) = 
  let STC g st x ty pre post = ct in
  (| ty, pre, x, post |)

let tm_exists_inversion (#g:env) (#u:universe) (#ty:term) (#p:term) 
                        (_:tot_typing g (tm_exists_sl u (as_binder ty) p) tm_vprop)
                        (x:var { fresh_wrt x g (freevars p) } )
  : universe_of g ty u &
    tot_typing (push_binding g x ppname_default ty) p tm_vprop
  = admit(), admit()

let tot_typing_weakening #g #t #ty x b d = admit()

let pure_typing_inversion (#g:env) (#p:term) (_:tot_typing g (tm_pure p) tm_vprop)
   : tot_typing g p (tm_fstar FStar.Reflection.Typing.tm_prop Range.range_0)
   = admit ()

let non_informative_t_weakening (g g':env) (g1:env{ pairwise_disjoint g g1 g' })
  (u:universe) (t:term)
  (d:non_informative_t (push_env g g') u t)
  : non_informative_t (push_env (push_env g g1) g') u t =
  let (| w, _ |) = d in
  (| w, magic () |)

let non_informative_c_weakening (g g':env) (g1:env{ pairwise_disjoint g g1 g' })
  (c:comp_st)
  (d:non_informative_c (push_env g g') c)
  : non_informative_c (push_env (push_env g g1) g') c =
  non_informative_t_weakening g g' g1 _ _ d

let bind_comp_weakening (g:env) (g':env { disjoint g g' })
  (#x:var) (#c1 #c2 #c3:comp) (d:bind_comp (push_env g g') x c1 c2 c3)
  (g1:env { pairwise_disjoint g g1 g' })
  : Tot (bind_comp (push_env (push_env g g1) g') x c1 c2 c3)
        (decreases d) =
  
  match d with
  | Bind_comp _ x c1 c2 _ _ _ ->
    assume (None? (lookup (push_env g g1) x));
    Bind_comp _ x c1 c2 (magic ()) (magic ()) (magic ())

  | Bind_comp_ghost_l _ x c1 c2 n_d _ _ _ ->
    assume (None? (lookup (push_env g g1) x));
    Bind_comp_ghost_l _ x c1 c2 (non_informative_c_weakening g g' g1 _ n_d) (magic ()) (magic ()) (magic ())

  | Bind_comp_ghost_r _ x c1 c2 n_d _ _ _ ->
    assume (None? (lookup (push_env g g1) x));
    Bind_comp_ghost_r _ x c1 c2 (non_informative_c_weakening g g' g1 _ n_d) (magic ()) (magic ()) (magic ())

let lift_comp_weakening (g:env) (g':env { disjoint g g'})
  (#c1 #c2:comp) (d:lift_comp (push_env g g') c1 c2)
  (g1:env { pairwise_disjoint g g1 g' })
  : Tot (lift_comp (push_env (push_env g g1) g') c1 c2)
        (decreases d) =
  
  match d with
  | Lift_STAtomic_ST _ c -> Lift_STAtomic_ST _ c
  | Lift_STGhost_STAtomic _ c non_informative_c ->
    Lift_STGhost_STAtomic _ c (non_informative_c_weakening g g' g1 _ non_informative_c)

let st_equiv_weakening (g:env) (g':env { disjoint g g' })
  (#c1 #c2:comp) (d:st_equiv (push_env g g') c1 c2)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_equiv (push_env (push_env g g1) g') c1 c2 =
  match d with
  | ST_VPropEquiv _ c1 c2 x _ _ _ _ _ ->
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    ST_VPropEquiv _ c1 c2 x (magic ()) (magic ()) (magic ()) (magic ()) (magic ())

let st_comp_typing_weakening (g:env) (g':env { disjoint g g' })
  (#s:st_comp) (d:st_comp_typing (push_env g g') s)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_comp_typing (push_env (push_env g g1) g') s =
  match d with
  | STC _ st x _ _ _ ->
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    STC _ st x (magic ()) (magic ()) (magic ())

let comp_typing_weakening (g:env) (g':env { disjoint g g' })
  (#c:comp) (#u:universe) (d:comp_typing (push_env g g') c u)
  (g1:env { pairwise_disjoint g g1 g' })
  : comp_typing (push_env (push_env g g1) g') c u =
  match d with
  | CT_Tot _ t u _ -> CT_Tot _ t u (magic ())
  | CT_ST _ _ d -> CT_ST _ _ (st_comp_typing_weakening g g' d g1)
  | CT_STAtomic _ inames _ _ d ->
    CT_STAtomic _ inames _ (magic ()) (st_comp_typing_weakening g g' d g1)
  | CT_STGhost _ inames _ _ d ->
    CT_STGhost _ inames _ (magic ()) (st_comp_typing_weakening g g' d g1)
  
#push-options "--z3rlimit_factor 4 --fuel 1 --ifuel 1"
let rec st_typing_weakening g g' t c d g1
  : Tot (st_typing (push_env (push_env g g1) g') t c)
        (decreases d) =
  
  match d with
  | T_Abs _ _ _ _ _ _ _ _ _ ->
    // T_Abs is used only at the top, should not come up
    magic ()

  | T_STApp _ head ty q res arg _ _ ->
    T_STApp _ head ty q res arg (magic ()) (magic ())

  | T_Return _ c use_eq u t e post x_old _ _ _ ->
    let x = fresh (push_env (push_env g g1) g') in
    assume (~ (x `Set.mem` freevars post));
    // x is only used to open and then close
    assume (comp_return c use_eq u t e post x_old ==
            comp_return c use_eq u t e post x);
    T_Return _ c use_eq u t e post x (magic ()) (magic ()) (magic ())

  | T_Lift _ e c1 c2 d_c1 d_lift ->
    T_Lift _ e c1 c2 (st_typing_weakening g g' e c1 d_c1 g1)
                     (lift_comp_weakening g g' d_lift g1)

  | T_Bind _ e1 e2 c1 c2 b x c d_e1 _ d_e2 d_bc ->
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
    T_Bind _ e1 e2 c1 c2 b x c d_e1 (magic ()) d_e2 d_bc

  | T_TotBind _ e1 e2 t1 c2 x _ d_e2 ->
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    let d_e2
      : st_typing (push_binding (push_env g g') x ppname_default t1)
                  (open_st_term_nv e2 (v_as_nv x))
                  c2 = d_e2 in
    assert (equal (push_binding (push_env g g') x ppname_default t1)
                  (push_env g (push_binding g' x ppname_default t1)));
    let d_e2
      : st_typing (push_env g (push_binding g' x ppname_default t1))
                  (open_st_term_nv e2 (v_as_nv x))
                  c2 = d_e2 in
    let d_e2
      : st_typing (push_env (push_env g g1) (push_binding g' x ppname_default t1))
                  (open_st_term_nv e2 (v_as_nv x))
                  c2 = st_typing_weakening g (push_binding g' x ppname_default t1) _ _ d_e2 g1 in
    assert (equal (push_env (push_env g g1) (push_binding g' x ppname_default t1))
                  (push_binding (push_env (push_env g g1) g') x ppname_default t1));
    let d_e2
      : st_typing (push_binding (push_env (push_env g g1) g') x ppname_default t1)
                  (open_st_term_nv e2 (v_as_nv x))
                  c2 = d_e2 in
    
    T_TotBind _ e1 e2 t1 c2 x (magic ()) d_e2

  | T_If _ b e1 e2 c uc hyp _ d_e1 d_e2 _ ->
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

    T_If _ b e1 e2 c uc hyp (magic ()) d_e1 d_e2 (magic ())

  | T_Frame _ e c frame _ d_e ->
    T_Frame _ e c frame (magic ()) (st_typing_weakening g g' e c d_e g1)

  | T_Equiv _ e c c' d_e d_eq ->
    T_Equiv _ e c c' (st_typing_weakening g g' e c d_e g1) (st_equiv_weakening g g' d_eq g1)

  | T_IntroPure _ p _ _ -> T_IntroPure _ p (magic ()) (magic ())

  | T_ElimExists _ u t p x _ _ ->
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    T_ElimExists _ u t p x (magic ()) (magic ())

  | T_IntroExists _ u b p e _ _ _ ->
    T_IntroExists _ u b p e (magic ()) (magic ()) (magic ())

  | T_IntroExistsErased _ u b p e _ _ _ ->
    T_IntroExistsErased _ u b p e (magic ()) (magic ()) (magic ())

  | T_While _ inv cond body _ cond_typing body_typing ->
    T_While _ inv cond body (magic ())
      (st_typing_weakening g g' cond (comp_while_cond ppname_default inv) cond_typing g1)
      (st_typing_weakening g g' body (comp_while_body ppname_default inv) body_typing g1)

  | T_Par _ eL cL eR cR x cL_typing cR_typing eL_typing eR_typing ->
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    T_Par _ eL cL eR cR x
      (comp_typing_weakening g g' cL_typing g1)
      (comp_typing_weakening g g' cR_typing g1)
      (st_typing_weakening g g' eL cL eL_typing g1)
      (st_typing_weakening g g' eR cR eR_typing g1)

  | T_WithLocal _ init body init_t c x _ _ d_c d_body ->
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
    T_WithLocal _ init body init_t c x (magic ()) (magic ())
      (comp_typing_weakening g g' d_c g1)
      d_body
  
  | T_Rewrite _ p q _ _ -> T_Rewrite _ p q (magic ()) (magic ())

  | T_Admit _ s c d_s -> T_Admit _ s c (st_comp_typing_weakening g g' d_s g1)
#pop-options

#push-options "--admit_smt_queries true"
let rec subst_env (en:env) (ss:subst)
  : en':env { fstar_env en == fstar_env en' /\
              dom en == dom en' } =
  match bindings en with
  | [] -> en
  | _ ->
    let x, t, en = remove_latest_binding en in
    push_binding (subst_env en ss) x ppname_default (subst_term t ss) 

let non_informative_t_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (u:universe) (t1:term)
  (d:non_informative_t (push_env g (push_env (singleton_env (fstar_env g) x t) g')) u t1)

  : non_informative_t (push_env g (subst_env g' (nt x e))) u (subst_term t1 (nt x e)) =

  let ss = nt x e in

  let (| w, _ |) = d in
  (| subst_term w ss, magic () |)

let non_informative_c_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (c:comp)
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

  | Lift_STGhost_STAtomic _ c d_non_informative ->
    Lift_STGhost_STAtomic _ (subst_comp c ss)
      (non_informative_c_subst g x t g' e_typing _ d_non_informative)

let bind_comp_subst
  (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#y:var) (#c1 #c2 #c3:comp) (d:bind_comp (push_env g (push_env (singleton_env (fstar_env g) x t) g')) y c1 c2 c3)
  : bind_comp (push_env g (subst_env g' (nt x e)))
              y
              (subst_comp c1 (nt x e))
              (subst_comp c2 (nt x e))
              (subst_comp c3 (nt x e)) =
  
  let ss = nt x e in

  match d with
  | Bind_comp _ y c1 c2 _ z _ ->
    Bind_comp _ y (subst_comp c1 ss)
                  (subst_comp c2 ss)
                  (magic ())
                  z
                  (magic ())
  
  | Bind_comp_ghost_l _ y c1 c2 d_non_informative _ z _ ->
    Bind_comp_ghost_l _ y (subst_comp c1 ss)
                          (subst_comp c2 ss)
                          (non_informative_c_subst g x t g' e_typing _ d_non_informative)
                          (magic ())
                          z
                          (magic ())

  | Bind_comp_ghost_r _ y c1 c2 d_non_informative _ z _ ->
    Bind_comp_ghost_r _ y (subst_comp c1 ss)
                          (subst_comp c2 ss)
                          (non_informative_c_subst g x t g' e_typing _ d_non_informative)
                          (magic ())
                          z
                          (magic ())

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b { y == x } = x

let rec st_typing_subst g x t g' #e e_typing #e1 #c1 e1_typing
  : Tot (st_typing (push_env g (subst_env g' (nt x e)))
                   (subst_st_term e1 (nt x e))
                   (subst_comp c1 (nt x e)))
        (decreases e1_typing) =
  
  let ss = nt x e in

  match e1_typing with
  | T_Abs _ _ _ _ _ _ _ _ _ -> magic ()

  | T_STApp _ head ty q res arg _ _ ->
    T_STApp _ (subst_term head ss)
              (subst_term ty ss)
              q
              (subst_comp res ss)
              (subst_term arg ss)
              (magic ())
              (magic ())

  | T_Return _ c use_eq u t e post x _ _ _ ->
    T_Return _ c use_eq u
      (subst_term t ss)
      (subst_term e ss)
      (subst_term post ss)
      x
      (magic ())
      (magic ())
      (magic ())

  | T_Lift _ e c1 c2 d_e d_lift ->
    T_Lift _ (subst_st_term e ss)
             (subst_comp c1 ss)
             (subst_comp c2 ss)
             (st_typing_subst g x t g' e_typing d_e)
             (lift_comp_subst g x t g' e_typing d_lift)

  | T_Bind _ e1 e2 c1 c2 b y c d_e1 _ d_e2 d_bc ->
    T_Bind _ (subst_st_term e1 ss)
             (subst_st_term e2 ss)
             (subst_comp c1 ss)
             (subst_comp c2 ss)
             (subst_binder b ss)
             y
             (subst_comp c ss)
             (st_typing_subst g x t g' e_typing d_e1)
             (magic ())
             (coerce_eq (st_typing_subst g x t (push_binding g' y ppname_default (comp_res c1)) e_typing d_e2) ())
             (bind_comp_subst g x t g' e_typing d_bc)

  | T_TotBind _ e1 e2 t1 c2 y _ d_e2 ->
    T_TotBind _ (subst_term e1 ss)
                (subst_st_term e2 ss)
                (subst_term t1 ss)
                (subst_comp c2 ss)
                y
                (magic ())
                (coerce_eq (st_typing_subst g x t (push_binding g' y ppname_default t1) e_typing d_e2) ())

  | T_If _ b e1 e2 c uc hyp _ d_e1 d_e2 _ ->
    T_If _ (subst_term b ss)
           (subst_st_term e1 ss)
           (subst_st_term e2 ss)
           (subst_comp c ss)
           uc
           hyp
           (magic ())
           (coerce_eq (st_typing_subst g x t (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_true)) e_typing d_e1) ())
           (coerce_eq (st_typing_subst g x t (push_binding g' hyp ppname_default (mk_eq2 u0 tm_bool b tm_false)) e_typing d_e2) ())
           (magic ())

  | T_Frame _ e c frame _ d_e ->
    T_Frame _ (subst_st_term e ss)
              (subst_comp c ss)
              (subst_term frame ss)
              (magic ())
              (st_typing_subst g x t g' e_typing d_e)

  | T_Equiv _ e c c' d_e _ ->
    T_Equiv _ (subst_st_term e ss)
              (subst_comp c ss)
              (subst_comp c' ss)
              (st_typing_subst g x t g' e_typing d_e)
              (magic ())

  | T_IntroPure _ p _ _ ->
    T_IntroPure _ (subst_term p ss)
                  (magic ())
                  (magic ())

  | T_ElimExists _ u t p y _ _ ->
    T_ElimExists _ u (subst_term t ss) (subst_term p ss) y (magic ()) (magic ())

  | T_IntroExists _ u b p e _ _ _ ->
    T_IntroExists _ u (subst_binder b ss)
                      (subst_term p ss)
                      (subst_term e ss)
                      (magic ())
                      (magic ())
                      (magic ())

  | T_IntroExistsErased _ u b p e _ _ _ ->
    T_IntroExistsErased _ u (subst_binder b ss)
                            (subst_term p ss)
                            (subst_term e ss)
                            (magic ())
                            (magic ())
                            (magic ())

  | T_While _ inv cond body _ cond_typing body_typing ->
    T_While _ (subst_term inv ss)
              (subst_st_term cond ss)
              (subst_st_term body ss)
              (magic ())
              (st_typing_subst g x t g' e_typing cond_typing)
              (st_typing_subst g x t g' e_typing body_typing)

  | T_Par _ eL cL eR cR y _ _ d_eL d_eR ->
    T_Par _ (subst_st_term eL ss)
            (subst_comp cL ss)
            (subst_st_term eR ss)
            (subst_comp cR ss)
            y
            (magic ())
            (magic ())
            (st_typing_subst g x t g' e_typing d_eL)
            (st_typing_subst g x t g' e_typing d_eR)

  | T_WithLocal _ init body init_t c y _ _ _ d_body ->
    T_WithLocal _ (subst_term init ss)
                  (subst_st_term body ss)
                  (subst_term init_t ss)
                  (subst_comp c ss)
                  y
                  (magic ())
                  (magic ())
                  (magic ())
                  (coerce_eq (st_typing_subst g x t (push_binding g' y ppname_default (mk_ref init_t)) e_typing d_body) ())

  | T_Rewrite _ p q _ _ ->
    T_Rewrite _ (subst_term p ss)
                (subst_term q ss)
                (magic ())
                (magic ())

  | T_Admit _ s c _ ->
    T_Admit _ (subst_st_comp s ss) c (magic ())
#pop-options
