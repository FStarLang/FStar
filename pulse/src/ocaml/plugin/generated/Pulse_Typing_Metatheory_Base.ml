open Prims
type ('g, 'c) comp_typing_u = (unit, unit, unit) Pulse_Typing.comp_typing
let (admit_st_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_comp -> (unit, unit) Pulse_Typing.st_comp_typing)
  =
  fun g ->
    fun st ->
      Pulse_Typing.STC (g, st, (Pulse_Typing_Env.fresh g), (), (), ())
let (admit_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st -> (unit, unit) comp_typing_u)
  =
  fun g ->
    fun c ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Typing.CT_ST (g, st, (admit_st_comp_typing g st))
      | Pulse_Syntax_Base.C_STAtomic (inames, st) ->
          Pulse_Typing.CT_STAtomic
            (g, inames, st, (), (admit_st_comp_typing g st))
      | Pulse_Syntax_Base.C_STGhost (inames, st) ->
          Pulse_Typing.CT_STGhost
            (g, inames, st, (), (admit_st_comp_typing g st))
let (st_typing_correctness :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (unit, unit) comp_typing_u)
  = fun g -> fun t -> fun c -> fun uu___ -> admit_comp_typing g c
let (add_frame_well_typed :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) comp_typing_u ->
        Pulse_Syntax_Base.term -> unit -> (unit, unit) comp_typing_u)
  =
  fun g ->
    fun c ->
      fun ct ->
        fun f -> fun ft -> admit_comp_typing g (Pulse_Typing.add_frame c f)
let (comp_typing_inversion :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) comp_typing_u -> (unit, unit) Pulse_Typing.st_comp_typing)
  =
  fun g ->
    fun c ->
      fun ct ->
        match ct with
        | Pulse_Typing.CT_ST (uu___, uu___1, st) -> st
        | Pulse_Typing.CT_STAtomic (uu___, uu___1, uu___2, uu___3, st) -> st
        | Pulse_Typing.CT_STGhost (uu___, uu___1, uu___2, uu___3, st) -> st
let (st_comp_typing_inversion_cofinite :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_comp ->
      (unit, unit) Pulse_Typing.st_comp_typing -> (unit * unit * unit))
  = fun g -> fun st -> fun ct -> ((), (), ())
let (st_comp_typing_inversion :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_comp ->
      (unit, unit) Pulse_Typing.st_comp_typing ->
        (unit, unit, Pulse_Syntax_Base.var, unit) FStar_Pervasives.dtuple4)
  =
  fun g ->
    fun st ->
      fun ct ->
        let uu___ = ct in
        match uu___ with
        | Pulse_Typing.STC (g1, st1, x, ty, pre, post) ->
            FStar_Pervasives.Mkdtuple4 ((), (), x, ())
let (tm_exists_inversion :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          unit -> Pulse_Syntax_Base.var -> (unit * unit))
  = fun g -> fun u -> fun ty -> fun p -> fun uu___ -> fun x -> ((), ())


let (non_informative_t_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.term ->
            (unit, unit, unit) Pulse_Typing.non_informative_t ->
              (unit, unit, unit) Pulse_Typing.non_informative_t)
  =
  fun g ->
    fun g' ->
      fun g1 ->
        fun u ->
          fun t ->
            fun d ->
              let uu___ = d in
              match uu___ with
              | Prims.Mkdtuple2 (w, uu___1) -> Prims.Mkdtuple2 (w, ())
let (non_informative_c_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.comp_st ->
          (unit, unit) Pulse_Typing.non_informative_c ->
            (unit, unit) Pulse_Typing.non_informative_c)
  =
  fun g ->
    fun g' ->
      fun g1 ->
        fun c ->
          fun d ->
            non_informative_t_weakening g g' g1 (Pulse_Syntax_Base.comp_u c)
              (Pulse_Syntax_Base.comp_res c) d
let (bind_comp_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.var ->
        Pulse_Syntax_Base.comp ->
          Pulse_Syntax_Base.comp ->
            Pulse_Syntax_Base.comp ->
              (unit, unit, unit, unit, unit) Pulse_Typing.bind_comp ->
                Pulse_Typing_Env.env ->
                  (unit, unit, unit, unit, unit) Pulse_Typing.bind_comp)
  =
  fun g ->
    fun g' ->
      fun x ->
        fun c1 ->
          fun c2 ->
            fun c3 ->
              fun d ->
                fun g1 ->
                  match d with
                  | Pulse_Typing.Bind_comp
                      (uu___, x1, c11, c21, uu___1, uu___2, uu___3) ->
                      let y =
                        Pulse_Typing_Env.fresh
                          (Pulse_Typing_Env.push_env
                             (Pulse_Typing_Env.push_env g g1) g') in
                      Pulse_Typing.Bind_comp
                        ((Pulse_Typing_Env.push_env
                            (Pulse_Typing_Env.push_env g g1) g'), x1, c11,
                          c21, (), y, ())
                  | Pulse_Typing.Bind_comp_ghost_l
                      (uu___, x1, c11, c21, n_d, uu___1, uu___2, uu___3) ->
                      let y =
                        Pulse_Typing_Env.fresh
                          (Pulse_Typing_Env.push_env
                             (Pulse_Typing_Env.push_env g g1) g') in
                      Pulse_Typing.Bind_comp_ghost_l
                        ((Pulse_Typing_Env.push_env
                            (Pulse_Typing_Env.push_env g g1) g'), x1, c11,
                          c21, (non_informative_c_weakening g g' g1 c11 n_d),
                          (), y, ())
                  | Pulse_Typing.Bind_comp_ghost_r
                      (uu___, x1, c11, c21, n_d, uu___1, uu___2, uu___3) ->
                      let y =
                        Pulse_Typing_Env.fresh
                          (Pulse_Typing_Env.push_env
                             (Pulse_Typing_Env.push_env g g1) g') in
                      Pulse_Typing.Bind_comp_ghost_r
                        ((Pulse_Typing_Env.push_env
                            (Pulse_Typing_Env.push_env g g1) g'), x1, c11,
                          c21, (non_informative_c_weakening g g' g1 c21 n_d),
                          (), y, ())
let (lift_comp_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.comp ->
          (unit, unit, unit) Pulse_Typing.lift_comp ->
            Pulse_Typing_Env.env -> (unit, unit, unit) Pulse_Typing.lift_comp)
  =
  fun g ->
    fun g' ->
      fun c1 ->
        fun c2 ->
          fun d ->
            fun g1 ->
              match d with
              | Pulse_Typing.Lift_STAtomic_ST (uu___, c) ->
                  Pulse_Typing.Lift_STAtomic_ST
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), c)
              | Pulse_Typing.Lift_STGhost_STAtomic
                  (uu___, c, non_informative_c) ->
                  Pulse_Typing.Lift_STGhost_STAtomic
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), c,
                      (non_informative_c_weakening g g' g1 c
                         non_informative_c))
let (st_equiv_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.comp ->
          (unit, unit, unit) Pulse_Typing.st_equiv ->
            Pulse_Typing_Env.env -> (unit, unit, unit) Pulse_Typing.st_equiv)
  =
  fun g ->
    fun g' ->
      fun c1 ->
        fun c2 ->
          fun d ->
            fun g1 ->
              match d with
              | Pulse_Typing.ST_VPropEquiv
                  (uu___, c11, c21, x, uu___1, uu___2, uu___3, uu___4,
                   uu___5)
                  ->
                  Pulse_Typing.ST_VPropEquiv
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), c11, c21, x,
                      (), (), (), (), ())
let (st_comp_typing_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_comp ->
        (unit, unit) Pulse_Typing.st_comp_typing ->
          Pulse_Typing_Env.env -> (unit, unit) Pulse_Typing.st_comp_typing)
  =
  fun g ->
    fun g' ->
      fun s ->
        fun d ->
          fun g1 ->
            match d with
            | Pulse_Typing.STC (uu___, st, x, uu___1, uu___2, uu___3) ->
                Pulse_Typing.STC
                  ((Pulse_Typing_Env.push_env
                      (Pulse_Typing_Env.push_env g g1) g'), st, x, (), (),
                    ())
let (comp_typing_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.universe ->
          (unit, unit, unit) Pulse_Typing.comp_typing ->
            Pulse_Typing_Env.env ->
              (unit, unit, unit) Pulse_Typing.comp_typing)
  =
  fun g ->
    fun g' ->
      fun c ->
        fun u ->
          fun d ->
            fun g1 ->
              match d with
              | Pulse_Typing.CT_Tot (uu___, t, u1, uu___1) ->
                  Pulse_Typing.CT_Tot
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), t, u1, ())
              | Pulse_Typing.CT_ST (uu___, uu___1, d1) ->
                  Pulse_Typing.CT_ST
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), uu___1,
                      (st_comp_typing_weakening g g' uu___1 d1 g1))
              | Pulse_Typing.CT_STAtomic (uu___, inames, uu___1, uu___2, d1)
                  ->
                  Pulse_Typing.CT_STAtomic
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), inames, uu___1,
                      (), (st_comp_typing_weakening g g' uu___1 d1 g1))
              | Pulse_Typing.CT_STGhost (uu___, inames, uu___1, uu___2, d1)
                  ->
                  Pulse_Typing.CT_STGhost
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), inames, uu___1,
                      (), (st_comp_typing_weakening g g' uu___1 d1 g1))
let (prop_validity_token_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (unit, unit) Pulse_Typing.prop_validity ->
        Pulse_Typing_Env.env -> (unit, unit) Pulse_Typing.prop_validity)
  = fun g -> fun t -> fun token -> fun g1 -> token
let rec (st_typing_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Typing_Env.env -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun g' ->
      fun t ->
        fun c ->
          fun d ->
            fun g1 ->
              match d with
              | Pulse_Typing.T_Abs
                  (uu___, uu___1, uu___2, uu___3, uu___4, uu___5, uu___6,
                   uu___7, uu___8)
                  -> Prims.magic ()
              | Pulse_Typing.T_STApp
                  (uu___, head, ty, q, res, arg, uu___1, uu___2) ->
                  Pulse_Typing.T_STApp
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), head, ty, q,
                      res, arg, (), ())
              | Pulse_Typing.T_Return
                  (uu___, c1, use_eq, u, t1, e, post, x_old, uu___1, uu___2,
                   uu___3)
                  ->
                  let x =
                    Pulse_Typing_Env.fresh
                      (Pulse_Typing_Env.push_env
                         (Pulse_Typing_Env.push_env g g1) g') in
                  Pulse_Typing.T_Return
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), c1, use_eq, u,
                      t1, e, post, x, (), (), ())
              | Pulse_Typing.T_Lift (uu___, e, c1, c2, d_c1, d_lift) ->
                  Pulse_Typing.T_Lift
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), e, c1, c2,
                      (st_typing_weakening g g' e c1 d_c1 g1),
                      (lift_comp_weakening g g' c1 c2 d_lift g1))
              | Pulse_Typing.T_Bind
                  (uu___, e1, e2, c1, c2, b, x, c3, d_e1, uu___1, d_e2, d_bc)
                  ->
                  let d_e11 = st_typing_weakening g g' e1 c1 d_e1 g1 in
                  let d_e21 = d_e2 in
                  let d_e22 = d_e21 in
                  let d_e23 =
                    st_typing_weakening g
                      (Pulse_Typing_Env.push_binding g' x
                         Pulse_Syntax_Base.ppname_default
                         (Pulse_Syntax_Base.comp_res c1))
                      (Pulse_Syntax_Naming.open_st_term_nv e2
                         ((b.Pulse_Syntax_Base.binder_ppname), x)) c2 d_e22
                      g1 in
                  let d_e24 = d_e23 in
                  let d_bc1 = bind_comp_weakening g g' x c1 c2 c3 d_bc g1 in
                  Pulse_Typing.T_Bind
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), e1, e2, c1, c2,
                      b, x, c3, d_e11, (), d_e24, d_bc1)
              | Pulse_Typing.T_TotBind
                  (uu___, e1, e2, t1, c2, x, uu___1, d_e2) ->
                  let d_e21 = d_e2 in
                  let d_e22 = d_e21 in
                  let d_e23 =
                    st_typing_weakening g
                      (Pulse_Typing_Env.push_binding g' x
                         Pulse_Syntax_Base.ppname_default t1)
                      (Pulse_Syntax_Naming.open_st_term_nv e2
                         (Pulse_Syntax_Base.v_as_nv x)) c2 d_e22 g1 in
                  let d_e24 = d_e23 in
                  Pulse_Typing.T_TotBind
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), e1, e2, t1, c2,
                      x, (), d_e24)
              | Pulse_Typing.T_If
                  (uu___, b, e1, e2, c1, uc, hyp, uu___1, d_e1, d_e2, uu___2)
                  ->
                  let d_e11 = d_e1 in
                  let d_e12 = d_e11 in
                  let d_e13 =
                    st_typing_weakening g
                      (Pulse_Typing_Env.push_binding g' hyp
                         Pulse_Syntax_Base.ppname_default
                         (Pulse_Typing.mk_eq2 Pulse_Syntax_Pure.u0
                            Pulse_Typing.tm_bool b Pulse_Typing.tm_true)) e1
                      c1 d_e12 g1 in
                  let d_e14 = d_e13 in
                  let d_e21 = d_e2 in
                  let d_e22 = d_e21 in
                  let d_e23 =
                    st_typing_weakening g
                      (Pulse_Typing_Env.push_binding g' hyp
                         Pulse_Syntax_Base.ppname_default
                         (Pulse_Typing.mk_eq2 Pulse_Syntax_Pure.u0
                            Pulse_Typing.tm_bool b Pulse_Typing.tm_false)) e2
                      c1 d_e22 g1 in
                  let d_e24 = d_e23 in
                  Pulse_Typing.T_If
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), b, e1, e2, c1,
                      uc, hyp, (), d_e14, d_e24, ())
              | Pulse_Typing.T_Match
                  (uu___, sc_u, sc_ty, sc, d_sc_ty, d_sc, c1, brs, d_brs,
                   d_pats_complete)
                  -> Prims.magic ()
              | Pulse_Typing.T_Frame (uu___, e, c1, frame, uu___1, d_e) ->
                  Pulse_Typing.T_Frame
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), e, c1, frame,
                      (), (st_typing_weakening g g' e c1 d_e g1))
              | Pulse_Typing.T_Equiv (uu___, e, c1, c', d_e, d_eq) ->
                  Pulse_Typing.T_Equiv
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), e, c1, c',
                      (st_typing_weakening g g' e c1 d_e g1),
                      (st_equiv_weakening g g' c1 c' d_eq g1))
              | Pulse_Typing.T_IntroPure (uu___, p, uu___1, token) ->
                  Pulse_Typing.T_IntroPure
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), p, (),
                      (prop_validity_token_weakening uu___ p token
                         (Pulse_Typing_Env.push_env
                            (Pulse_Typing_Env.push_env g g1) g')))
              | Pulse_Typing.T_ElimExists
                  (uu___, u, t1, p, x, uu___1, uu___2) ->
                  Pulse_Typing.T_ElimExists
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), u, t1, p, x,
                      (), ())
              | Pulse_Typing.T_IntroExists
                  (uu___, u, b, p, e, uu___1, uu___2, uu___3) ->
                  Pulse_Typing.T_IntroExists
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), u, b, p, e, (),
                      (), ())
              | Pulse_Typing.T_IntroExistsErased
                  (uu___, u, b, p, e, uu___1, uu___2, uu___3) ->
                  Pulse_Typing.T_IntroExistsErased
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), u, b, p, e, (),
                      (), ())
              | Pulse_Typing.T_While
                  (uu___, inv, cond, body, uu___1, cond_typing, body_typing)
                  ->
                  Pulse_Typing.T_While
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), inv, cond,
                      body, (),
                      (st_typing_weakening g g' cond
                         (Pulse_Typing.comp_while_cond
                            Pulse_Syntax_Base.ppname_default inv) cond_typing
                         g1),
                      (st_typing_weakening g g' body
                         (Pulse_Typing.comp_while_body
                            Pulse_Syntax_Base.ppname_default inv) body_typing
                         g1))
              | Pulse_Typing.T_Par
                  (uu___, eL, cL, eR, cR, x, cL_typing, cR_typing, eL_typing,
                   eR_typing)
                  ->
                  Pulse_Typing.T_Par
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), eL, cL, eR, cR,
                      x,
                      (comp_typing_weakening g g' cL
                         (Pulse_Syntax_Base.comp_u cL) cL_typing g1),
                      (comp_typing_weakening g g' cR
                         (Pulse_Syntax_Base.comp_u cR) cR_typing g1),
                      (st_typing_weakening g g' eL cL eL_typing g1),
                      (st_typing_weakening g g' eR cR eR_typing g1))
              | Pulse_Typing.T_WithLocal
                  (uu___, init, body, init_t, c1, x, uu___1, uu___2, d_c,
                   d_body)
                  ->
                  let d_body1 = d_body in
                  let d_body2 = d_body1 in
                  let d_body3 =
                    st_typing_weakening g
                      (Pulse_Typing_Env.push_binding g' x
                         Pulse_Syntax_Base.ppname_default
                         (Pulse_Typing.mk_ref init_t))
                      (Pulse_Syntax_Naming.open_st_term_nv body
                         (Pulse_Syntax_Base.v_as_nv x))
                      (Pulse_Typing.comp_withlocal_body x init_t init c1)
                      d_body2 g1 in
                  let d_body4 = d_body3 in
                  Pulse_Typing.T_WithLocal
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), init, body,
                      init_t, c1, x, (), (),
                      (comp_typing_weakening g g' c1
                         (Pulse_Syntax_Base.comp_u c1) d_c g1), d_body4)
              | Pulse_Typing.T_Rewrite (uu___, p, q, uu___1, uu___2) ->
                  Pulse_Typing.T_Rewrite
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), p, q, (), ())
              | Pulse_Typing.T_Admit (uu___, s, c1, d_s) ->
                  Pulse_Typing.T_Admit
                    ((Pulse_Typing_Env.push_env
                        (Pulse_Typing_Env.push_env g g1) g'), s, c1,
                      (st_comp_typing_weakening g g' s d_s g1))
let (nt :
  Pulse_Syntax_Base.var ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Naming.subst_elt Prims.list)
  = fun x -> fun t -> [Pulse_Syntax_Naming.NT (x, t)]
let (non_informative_t_subst :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.typ ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.universe ->
                Pulse_Syntax_Base.term ->
                  (unit, unit, unit) Pulse_Typing.non_informative_t ->
                    (unit, unit, unit) Pulse_Typing.non_informative_t)
  =
  fun g ->
    fun x ->
      fun t ->
        fun g' ->
          fun e ->
            fun e_typing ->
              fun u ->
                fun t1 ->
                  fun d ->
                    let ss = nt x e in
                    let uu___ = d in
                    match uu___ with
                    | Prims.Mkdtuple2 (w, uu___1) ->
                        Prims.Mkdtuple2
                          ((Pulse_Syntax_Naming.subst_term w ss), ())
let (non_informative_c_subst :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.typ ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.comp ->
                (unit, unit) Pulse_Typing.non_informative_c ->
                  (unit, unit) Pulse_Typing.non_informative_c)
  =
  fun g ->
    fun x ->
      fun t ->
        fun g' ->
          fun e ->
            fun e_typing ->
              fun c ->
                fun d ->
                  non_informative_t_subst g x t g' e ()
                    (Pulse_Syntax_Base.comp_u c)
                    (Pulse_Syntax_Base.comp_res c) d
let (lift_comp_subst :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.typ ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.comp ->
                Pulse_Syntax_Base.comp ->
                  (unit, unit, unit) Pulse_Typing.lift_comp ->
                    (unit, unit, unit) Pulse_Typing.lift_comp)
  =
  fun g ->
    fun x ->
      fun t ->
        fun g' ->
          fun e ->
            fun e_typing ->
              fun c1 ->
                fun c2 ->
                  fun d ->
                    let ss = nt x e in
                    match d with
                    | Pulse_Typing.Lift_STAtomic_ST (uu___, c) ->
                        Pulse_Typing.Lift_STAtomic_ST
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_comp c ss))
                    | Pulse_Typing.Lift_STGhost_STAtomic
                        (uu___, c, d_non_informative) ->
                        Pulse_Typing.Lift_STGhost_STAtomic
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_comp c ss),
                            (non_informative_c_subst g x t g' e () c
                               d_non_informative))
let (bind_comp_subst :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.typ ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.var ->
                Pulse_Syntax_Base.comp ->
                  Pulse_Syntax_Base.comp ->
                    Pulse_Syntax_Base.comp ->
                      (unit, unit, unit, unit, unit) Pulse_Typing.bind_comp
                        ->
                        (unit, unit, unit, unit, unit) Pulse_Typing.bind_comp)
  =
  fun g ->
    fun x ->
      fun t ->
        fun g' ->
          fun e ->
            fun e_typing ->
              fun y ->
                fun c1 ->
                  fun c2 ->
                    fun c3 ->
                      fun d ->
                        let ss = nt x e in
                        match d with
                        | Pulse_Typing.Bind_comp
                            (uu___, y1, c11, c21, uu___1, z, uu___2) ->
                            Pulse_Typing.Bind_comp
                              ((Pulse_Typing_Env.push_env g
                                  (Pulse_Typing_Env.subst_env g' (nt x e))),
                                y1, (Pulse_Syntax_Naming.subst_comp c11 ss),
                                (Pulse_Syntax_Naming.subst_comp c21 ss), (),
                                z, ())
                        | Pulse_Typing.Bind_comp_ghost_l
                            (uu___, y1, c11, c21, d_non_informative, uu___1,
                             z, uu___2)
                            ->
                            Pulse_Typing.Bind_comp_ghost_l
                              ((Pulse_Typing_Env.push_env g
                                  (Pulse_Typing_Env.subst_env g' (nt x e))),
                                y1, (Pulse_Syntax_Naming.subst_comp c11 ss),
                                (Pulse_Syntax_Naming.subst_comp c21 ss),
                                (non_informative_c_subst g x t g' e () c11
                                   d_non_informative), (), z, ())
                        | Pulse_Typing.Bind_comp_ghost_r
                            (uu___, y1, c11, c21, d_non_informative, uu___1,
                             z, uu___2)
                            ->
                            Pulse_Typing.Bind_comp_ghost_r
                              ((Pulse_Typing_Env.push_env g
                                  (Pulse_Typing_Env.subst_env g' (nt x e))),
                                y1, (Pulse_Syntax_Naming.subst_comp c11 ss),
                                (Pulse_Syntax_Naming.subst_comp c21 ss),
                                (non_informative_c_subst g x t g' e () c21
                                   d_non_informative), (), z, ())
let (st_equiv_subst :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.typ ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.comp ->
                Pulse_Syntax_Base.comp ->
                  (unit, unit, unit) Pulse_Typing.st_equiv ->
                    (unit, unit, unit) Pulse_Typing.st_equiv)
  =
  fun g ->
    fun x ->
      fun t ->
        fun g' ->
          fun e ->
            fun e_typing ->
              fun c1 ->
                fun c2 ->
                  fun d ->
                    match d with
                    | Pulse_Typing.ST_VPropEquiv
                        (uu___, c11, c21, y, uu___1, uu___2, uu___3, uu___4,
                         uu___5)
                        ->
                        Pulse_Typing.ST_VPropEquiv
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_comp c11 (nt x e)),
                            (Pulse_Syntax_Naming.subst_comp c21 (nt x e)), y,
                            (), (), (), (), ())
let (st_comp_typing_subst :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.typ ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.st_comp ->
                (unit, unit) Pulse_Typing.st_comp_typing ->
                  (unit, unit) Pulse_Typing.st_comp_typing)
  =
  fun g ->
    fun x ->
      fun t ->
        fun g' ->
          fun e ->
            fun e_typing ->
              fun s ->
                fun d ->
                  match d with
                  | Pulse_Typing.STC (uu___, s1, y, uu___1, uu___2, uu___3)
                      ->
                      Pulse_Typing.STC
                        ((Pulse_Typing_Env.push_env g
                            (Pulse_Typing_Env.subst_env g' (nt x e))),
                          (Pulse_Syntax_Naming.subst_st_comp s1 (nt x e)), y,
                          (), (), ())
let (comp_typing_subst :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.typ ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.comp ->
                Pulse_Syntax_Base.universe ->
                  (unit, unit, unit) Pulse_Typing.comp_typing ->
                    (unit, unit, unit) Pulse_Typing.comp_typing)
  =
  fun g ->
    fun x ->
      fun t ->
        fun g' ->
          fun e ->
            fun e_typing ->
              fun c ->
                fun u ->
                  fun d ->
                    match d with
                    | Pulse_Typing.CT_Tot (uu___, t1, u1, uu___1) ->
                        Pulse_Typing.CT_Tot
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_term t1 (nt x e)), u1,
                            ())
                    | Pulse_Typing.CT_ST (uu___, s, d_s) ->
                        Pulse_Typing.CT_ST
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_st_comp s (nt x e)),
                            (st_comp_typing_subst g x t g' e () s d_s))
                    | Pulse_Typing.CT_STAtomic
                        (uu___, inames, s, uu___1, d_s) ->
                        Pulse_Typing.CT_STAtomic
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            inames,
                            (Pulse_Syntax_Naming.subst_st_comp s (nt x e)),
                            (), (st_comp_typing_subst g x t g' e () s d_s))
                    | Pulse_Typing.CT_STGhost (uu___, inames, s, uu___1, d_s)
                        ->
                        Pulse_Typing.CT_STGhost
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            inames,
                            (Pulse_Syntax_Naming.subst_st_comp s (nt x e)),
                            (), (st_comp_typing_subst g x t g' e () s d_s))
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let rec (st_typing_subst :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.typ ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.st_term ->
                Pulse_Syntax_Base.comp_st ->
                  (unit, unit, unit) Pulse_Typing.st_typing ->
                    (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun x ->
      fun t ->
        fun g' ->
          fun e ->
            fun e_typing ->
              fun e1 ->
                fun c1 ->
                  fun e1_typing ->
                    let ss = nt x e in
                    match e1_typing with
                    | Pulse_Typing.T_Abs
                        (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                         uu___6, uu___7, uu___8)
                        -> Prims.magic ()
                    | Pulse_Typing.T_STApp
                        (uu___, head, ty, q, res, arg, uu___1, uu___2) ->
                        Pulse_Typing.T_STApp
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_term head ss),
                            (Pulse_Syntax_Naming.subst_term ty ss), q,
                            (Pulse_Syntax_Naming.subst_comp res ss),
                            (Pulse_Syntax_Naming.subst_term arg ss), (), ())
                    | Pulse_Typing.T_Return
                        (uu___, c, use_eq, u, t1, e2, post, x1, uu___1,
                         uu___2, uu___3)
                        ->
                        Pulse_Typing.T_Return
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))), c,
                            use_eq, u,
                            (Pulse_Syntax_Naming.subst_term t1 ss),
                            (Pulse_Syntax_Naming.subst_term e2 ss),
                            (Pulse_Syntax_Naming.subst_term post ss), x1, (),
                            (), ())
                    | Pulse_Typing.T_Lift (uu___, e2, c11, c2, d_e, d_lift)
                        ->
                        Pulse_Typing.T_Lift
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_st_term e2 ss),
                            (Pulse_Syntax_Naming.subst_comp c11 ss),
                            (Pulse_Syntax_Naming.subst_comp c2 ss),
                            (st_typing_subst g x t g' e () e2 c11 d_e),
                            (lift_comp_subst g x t g' e () c11 c2 d_lift))
                    | Pulse_Typing.T_Bind
                        (uu___, e11, e2, c11, c2, b, y, c, d_e1, uu___1,
                         d_e2, d_bc)
                        ->
                        Pulse_Typing.T_Bind
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_st_term e11 ss),
                            (Pulse_Syntax_Naming.subst_st_term e2 ss),
                            (Pulse_Syntax_Naming.subst_comp c11 ss),
                            (Pulse_Syntax_Naming.subst_comp c2 ss),
                            (Pulse_Syntax_Naming.subst_binder b ss), y,
                            (Pulse_Syntax_Naming.subst_comp c ss),
                            (st_typing_subst g x t g' e () e11 c11 d_e1), (),
                            (coerce_eq
                               (st_typing_subst g x t
                                  (Pulse_Typing_Env.push_binding g' y
                                     Pulse_Syntax_Base.ppname_default
                                     (Pulse_Syntax_Base.comp_res c11)) e ()
                                  (Pulse_Syntax_Naming.open_st_term_nv e2
                                     ((b.Pulse_Syntax_Base.binder_ppname), y))
                                  c2 d_e2) ()),
                            (bind_comp_subst g x t g' e () y c11 c2 c d_bc))
                    | Pulse_Typing.T_TotBind
                        (uu___, e11, e2, t1, c2, y, uu___1, d_e2) ->
                        Pulse_Typing.T_TotBind
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_term e11 ss),
                            (Pulse_Syntax_Naming.subst_st_term e2 ss),
                            (Pulse_Syntax_Naming.subst_term t1 ss),
                            (Pulse_Syntax_Naming.subst_comp c2 ss), y, (),
                            (coerce_eq
                               (st_typing_subst g x t
                                  (Pulse_Typing_Env.push_binding g' y
                                     Pulse_Syntax_Base.ppname_default t1) e
                                  ()
                                  (Pulse_Syntax_Naming.open_st_term_nv e2
                                     (Pulse_Syntax_Base.v_as_nv y)) c2 d_e2)
                               ()))
                    | Pulse_Typing.T_If
                        (uu___, b, e11, e2, c, uc, hyp, uu___1, d_e1, d_e2,
                         uu___2)
                        ->
                        Pulse_Typing.T_If
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_term b ss),
                            (Pulse_Syntax_Naming.subst_st_term e11 ss),
                            (Pulse_Syntax_Naming.subst_st_term e2 ss),
                            (Pulse_Syntax_Naming.subst_comp c ss), uc, hyp,
                            (),
                            (coerce_eq
                               (st_typing_subst g x t
                                  (Pulse_Typing_Env.push_binding g' hyp
                                     Pulse_Syntax_Base.ppname_default
                                     (Pulse_Typing.mk_eq2
                                        Pulse_Syntax_Pure.u0
                                        Pulse_Typing.tm_bool b
                                        Pulse_Typing.tm_true)) e () e11 c
                                  d_e1) ()),
                            (coerce_eq
                               (st_typing_subst g x t
                                  (Pulse_Typing_Env.push_binding g' hyp
                                     Pulse_Syntax_Base.ppname_default
                                     (Pulse_Typing.mk_eq2
                                        Pulse_Syntax_Pure.u0
                                        Pulse_Typing.tm_bool b
                                        Pulse_Typing.tm_false)) e () e2 c
                                  d_e2) ()), ())
                    | Pulse_Typing.T_Match
                        (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                         uu___6, uu___7, uu___8, uu___9)
                        -> Prims.magic ()
                    | Pulse_Typing.T_Frame (uu___, e2, c, frame, uu___1, d_e)
                        ->
                        Pulse_Typing.T_Frame
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_st_term e2 ss),
                            (Pulse_Syntax_Naming.subst_comp c ss),
                            (Pulse_Syntax_Naming.subst_term frame ss), (),
                            (st_typing_subst g x t g' e () e2 c d_e))
                    | Pulse_Typing.T_Equiv (uu___, e2, c, c', d_e, d_eq) ->
                        Pulse_Typing.T_Equiv
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_st_term e2 ss),
                            (Pulse_Syntax_Naming.subst_comp c ss),
                            (Pulse_Syntax_Naming.subst_comp c' ss),
                            (st_typing_subst g x t g' e () e2 c d_e),
                            (st_equiv_subst g x t g' e () c c' d_eq))
                    | Pulse_Typing.T_IntroPure (uu___, p, uu___1, uu___2) ->
                        Pulse_Typing.T_IntroPure
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_term p ss), (),
                            (Prims.magic ()))
                    | Pulse_Typing.T_ElimExists
                        (uu___, u, t1, p, y, uu___1, uu___2) ->
                        Pulse_Typing.T_ElimExists
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))), u,
                            (Pulse_Syntax_Naming.subst_term t1 ss),
                            (Pulse_Syntax_Naming.subst_term p ss), y, (), ())
                    | Pulse_Typing.T_IntroExists
                        (uu___, u, b, p, e2, uu___1, uu___2, uu___3) ->
                        Pulse_Typing.T_IntroExists
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))), u,
                            (Pulse_Syntax_Naming.subst_binder b ss),
                            (Pulse_Syntax_Naming.subst_term p ss),
                            (Pulse_Syntax_Naming.subst_term e2 ss), (), (),
                            ())
                    | Pulse_Typing.T_IntroExistsErased
                        (uu___, u, b, p, e2, uu___1, uu___2, uu___3) ->
                        Pulse_Typing.T_IntroExistsErased
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))), u,
                            (Pulse_Syntax_Naming.subst_binder b ss),
                            (Pulse_Syntax_Naming.subst_term p ss),
                            (Pulse_Syntax_Naming.subst_term e2 ss), (), (),
                            ())
                    | Pulse_Typing.T_While
                        (uu___, inv, cond, body, uu___1, cond_typing,
                         body_typing)
                        ->
                        Pulse_Typing.T_While
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_term inv ss),
                            (Pulse_Syntax_Naming.subst_st_term cond ss),
                            (Pulse_Syntax_Naming.subst_st_term body ss), (),
                            (st_typing_subst g x t g' e () cond
                               (Pulse_Typing.comp_while_cond
                                  Pulse_Syntax_Base.ppname_default inv)
                               cond_typing),
                            (st_typing_subst g x t g' e () body
                               (Pulse_Typing.comp_while_body
                                  Pulse_Syntax_Base.ppname_default inv)
                               body_typing))
                    | Pulse_Typing.T_Par
                        (uu___, eL, cL, eR, cR, y, d_cL, d_cR, d_eL, d_eR) ->
                        Pulse_Typing.T_Par
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_st_term eL ss),
                            (Pulse_Syntax_Naming.subst_comp cL ss),
                            (Pulse_Syntax_Naming.subst_st_term eR ss),
                            (Pulse_Syntax_Naming.subst_comp cR ss), y,
                            (comp_typing_subst g x t g' e () cL
                               (Pulse_Syntax_Base.comp_u cL) d_cL),
                            (comp_typing_subst g x t g' e () cR
                               (Pulse_Syntax_Base.comp_u cR) d_cR),
                            (st_typing_subst g x t g' e () eL cL d_eL),
                            (st_typing_subst g x t g' e () eR cR d_eR))
                    | Pulse_Typing.T_WithLocal
                        (uu___, init, body, init_t, c, y, uu___1, uu___2,
                         d_c, d_body)
                        ->
                        Pulse_Typing.T_WithLocal
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_term init ss),
                            (Pulse_Syntax_Naming.subst_st_term body ss),
                            (Pulse_Syntax_Naming.subst_term init_t ss),
                            (Pulse_Syntax_Naming.subst_comp c ss), y, (), (),
                            (comp_typing_subst g x t g' e () c
                               (Pulse_Syntax_Base.comp_u c) d_c),
                            (coerce_eq
                               (st_typing_subst g x t
                                  (Pulse_Typing_Env.push_binding g' y
                                     Pulse_Syntax_Base.ppname_default
                                     (Pulse_Typing.mk_ref init_t)) e ()
                                  (Pulse_Syntax_Naming.open_st_term_nv body
                                     (Pulse_Syntax_Base.v_as_nv y))
                                  (Pulse_Typing.comp_withlocal_body y init_t
                                     init c) d_body) ()))
                    | Pulse_Typing.T_Rewrite (uu___, p, q, uu___1, uu___2) ->
                        Pulse_Typing.T_Rewrite
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_term p ss),
                            (Pulse_Syntax_Naming.subst_term q ss), (), ())
                    | Pulse_Typing.T_Admit (uu___, s, c, d_s) ->
                        Pulse_Typing.T_Admit
                          ((Pulse_Typing_Env.push_env g
                              (Pulse_Typing_Env.subst_env g' (nt x e))),
                            (Pulse_Syntax_Naming.subst_st_comp s ss), c,
                            (st_comp_typing_subst g x t g' e () s d_s))