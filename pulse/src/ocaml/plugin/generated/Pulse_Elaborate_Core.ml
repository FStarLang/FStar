open Prims
let (elab_frame :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun c ->
    fun frame ->
      fun e ->
        let u = Pulse_Syntax_Base.comp_u c in
        let ty =
          Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_res c) in
        let pre =
          Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_pre c) in
        let post =
          Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_post c) in
        if Pulse_Syntax_Base.uu___is_C_ST c
        then
          Pulse_Reflection_Util.mk_frame_stt u ty pre
            (Pulse_Reflection_Util.mk_abs ty FStar_Reflection_Data.Q_Explicit
               post) (Pulse_Elaborate_Pure.elab_term frame) e
        else
          (let opened =
             Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_inames c) in
           if Pulse_Syntax_Base.uu___is_C_STAtomic c
           then
             Pulse_Reflection_Util.mk_frame_stt_atomic u ty opened pre
               (Pulse_Reflection_Util.mk_abs ty
                  FStar_Reflection_Data.Q_Explicit post)
               (Pulse_Elaborate_Pure.elab_term frame) e
           else
             Pulse_Reflection_Util.mk_frame_stt_ghost u ty opened pre
               (Pulse_Reflection_Util.mk_abs ty
                  FStar_Reflection_Data.Q_Explicit post)
               (Pulse_Elaborate_Pure.elab_term frame) e)
let (elab_sub :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.comp_st ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun c1 ->
    fun c2 ->
      fun e ->
        let ty =
          Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_res c1) in
        let u = Pulse_Syntax_Base.comp_u c1 in
        let pre1 =
          Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_pre c1) in
        let pre2 =
          Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_pre c2) in
        let post1 =
          Pulse_Reflection_Util.mk_abs ty FStar_Reflection_Data.Q_Explicit
            (Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_post c1)) in
        let post2 =
          Pulse_Reflection_Util.mk_abs ty FStar_Reflection_Data.Q_Explicit
            (Pulse_Elaborate_Pure.elab_term (Pulse_Syntax_Base.comp_post c2)) in
        if Pulse_Syntax_Base.uu___is_C_ST c1
        then Pulse_Reflection_Util.mk_sub_stt u ty pre1 pre2 post1 post2 e
        else
          (let opened =
             Pulse_Elaborate_Pure.elab_term
               (Pulse_Syntax_Base.comp_inames c1) in
           if Pulse_Syntax_Base.uu___is_C_STAtomic c1
           then
             Pulse_Reflection_Util.mk_sub_stt_atomic u ty opened pre1 pre2
               post1 post2 e
           else
             Pulse_Reflection_Util.mk_sub_stt_ghost u ty opened pre1 pre2
               post1 post2 e)
let (elab_bind :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.comp ->
          Pulse_Syntax_Base.comp ->
            (unit, unit, unit, unit, unit) Pulse_Typing.bind_comp ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun g ->
    fun x ->
      fun c1 ->
        fun c2 ->
          fun c ->
            fun bc ->
              fun e1 ->
                fun e2 ->
                  let t1 =
                    Pulse_Elaborate_Pure.elab_term
                      (Pulse_Syntax_Base.comp_res c1) in
                  let t2 =
                    Pulse_Elaborate_Pure.elab_term
                      (Pulse_Syntax_Base.comp_res c2) in
                  match bc with
                  | Pulse_Typing.Bind_comp
                      (uu___, uu___1, uu___2, uu___3, uu___4, uu___5, uu___6)
                      ->
                      if Pulse_Syntax_Base.uu___is_C_ST c1
                      then
                        Pulse_Reflection_Util.mk_bind_stt
                          (Pulse_Syntax_Base.comp_u c1)
                          (Pulse_Syntax_Base.comp_u c2) t1 t2
                          (Pulse_Elaborate_Pure.elab_term
                             (Pulse_Syntax_Base.comp_pre c1))
                          (Pulse_Reflection_Util.mk_abs t1
                             FStar_Reflection_Data.Q_Explicit
                             (Pulse_Elaborate_Pure.elab_term
                                (Pulse_Syntax_Base.comp_post c1)))
                          (Pulse_Reflection_Util.mk_abs t2
                             FStar_Reflection_Data.Q_Explicit
                             (Pulse_Elaborate_Pure.elab_term
                                (Pulse_Syntax_Base.comp_post c2))) e1 e2
                      else
                        Pulse_Reflection_Util.mk_bind_ghost
                          (Pulse_Syntax_Base.comp_u c1)
                          (Pulse_Syntax_Base.comp_u c2) t1 t2
                          (Pulse_Elaborate_Pure.elab_term
                             (Pulse_Syntax_Base.comp_inames c1))
                          (Pulse_Elaborate_Pure.elab_term
                             (Pulse_Syntax_Base.comp_pre c1))
                          (Pulse_Reflection_Util.mk_abs t1
                             FStar_Reflection_Data.Q_Explicit
                             (Pulse_Elaborate_Pure.elab_term
                                (Pulse_Syntax_Base.comp_post c1)))
                          (Pulse_Reflection_Util.mk_abs t2
                             FStar_Reflection_Data.Q_Explicit
                             (Pulse_Elaborate_Pure.elab_term
                                (Pulse_Syntax_Base.comp_post c2))) e1 e2
                  | Pulse_Typing.Bind_comp_ghost_l
                      (uu___, uu___1, uu___2, uu___3, Prims.Mkdtuple2
                       (reveal_a, reveal_a_typing), uu___4, uu___5, uu___6)
                      ->
                      Pulse_Reflection_Util.mk_bind_ghost_atomic
                        (Pulse_Syntax_Base.comp_u c1)
                        (Pulse_Syntax_Base.comp_u c2) t1 t2
                        (Pulse_Elaborate_Pure.elab_term
                           (Pulse_Syntax_Base.comp_inames c1))
                        (Pulse_Elaborate_Pure.elab_term
                           (Pulse_Syntax_Base.comp_pre c1))
                        (Pulse_Reflection_Util.mk_abs t1
                           FStar_Reflection_Data.Q_Explicit
                           (Pulse_Elaborate_Pure.elab_term
                              (Pulse_Syntax_Base.comp_post c1)))
                        (Pulse_Reflection_Util.mk_abs t2
                           FStar_Reflection_Data.Q_Explicit
                           (Pulse_Elaborate_Pure.elab_term
                              (Pulse_Syntax_Base.comp_post c2))) e1 e2
                        (Pulse_Elaborate_Pure.elab_term reveal_a)
                  | Pulse_Typing.Bind_comp_ghost_r
                      (uu___, uu___1, uu___2, uu___3, Prims.Mkdtuple2
                       (reveal_b, reveal_b_typing), uu___4, uu___5, uu___6)
                      ->
                      Pulse_Reflection_Util.mk_bind_atomic_ghost
                        (Pulse_Syntax_Base.comp_u c1)
                        (Pulse_Syntax_Base.comp_u c2) t1 t2
                        (Pulse_Elaborate_Pure.elab_term
                           (Pulse_Syntax_Base.comp_inames c1))
                        (Pulse_Elaborate_Pure.elab_term
                           (Pulse_Syntax_Base.comp_pre c1))
                        (Pulse_Reflection_Util.mk_abs t1
                           FStar_Reflection_Data.Q_Explicit
                           (Pulse_Elaborate_Pure.elab_term
                              (Pulse_Syntax_Base.comp_post c1)))
                        (Pulse_Reflection_Util.mk_abs t2
                           FStar_Reflection_Data.Q_Explicit
                           (Pulse_Elaborate_Pure.elab_term
                              (Pulse_Syntax_Base.comp_post c2))) e1 e2
                        (Pulse_Elaborate_Pure.elab_term reveal_b)
let (elab_lift :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.comp ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.lift_comp ->
          FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun g ->
    fun c1 ->
      fun c2 ->
        fun d ->
          fun e ->
            match d with
            | Pulse_Typing.Lift_STAtomic_ST (uu___, uu___1) ->
                let t =
                  Pulse_Elaborate_Pure.elab_term
                    (Pulse_Syntax_Base.comp_res c1) in
                Pulse_Reflection_Util.mk_lift_atomic_stt
                  (Pulse_Syntax_Base.comp_u c1)
                  (Pulse_Elaborate_Pure.elab_term
                     (Pulse_Syntax_Base.comp_res c1)) t
                  (Pulse_Reflection_Util.mk_abs t
                     FStar_Reflection_Data.Q_Explicit
                     (Pulse_Elaborate_Pure.elab_term
                        (Pulse_Syntax_Base.comp_post c1))) e
            | Pulse_Typing.Lift_STGhost_STAtomic
                (uu___, uu___1, Prims.Mkdtuple2 (reveal_a, reveal_a_typing))
                ->
                let t =
                  Pulse_Elaborate_Pure.elab_term
                    (Pulse_Syntax_Base.comp_res c1) in
                Pulse_Reflection_Util.mk_lift_ghost_atomic
                  (Pulse_Syntax_Base.comp_u c1) t
                  (Pulse_Elaborate_Pure.elab_term
                     (Pulse_Syntax_Base.comp_inames c1))
                  (Pulse_Elaborate_Pure.elab_term
                     (Pulse_Syntax_Base.comp_pre c1))
                  (Pulse_Reflection_Util.mk_abs t
                     FStar_Reflection_Data.Q_Explicit
                     (Pulse_Elaborate_Pure.elab_term
                        (Pulse_Syntax_Base.comp_post c1))) e
                  (Pulse_Elaborate_Pure.elab_term reveal_a)
let (intro_pure_tm : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term) =
  fun p ->
    Pulse_Typing.wr
      (Pulse_Syntax_Base.Tm_STApp
         {
           Pulse_Syntax_Base.head =
             (Pulse_Syntax_Pure.tm_pureapp
                (Pulse_Syntax_Pure.tm_fvar
                   (Pulse_Syntax_Base.as_fv
                      (Pulse_Reflection_Util.mk_steel_wrapper_lid
                         "intro_pure"))) FStar_Pervasives_Native.None p);
           Pulse_Syntax_Base.arg_qual = FStar_Pervasives_Native.None;
           Pulse_Syntax_Base.arg =
             (Pulse_Syntax_Base.Tm_FStar
                ((FStar_Reflection_Builtins.pack_ln
                    (FStar_Reflection_Data.Tv_Const
                       FStar_Reflection_Data.C_Unit)), FStar_Range.range_0))
         })
let rec (elab_st_typing :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          FStar_Reflection_Types.term)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          match d with
          | Pulse_Typing.T_Abs
              (uu___, x, qual, b, _u, body, _c, ty_typing, body_typing) ->
              let ty =
                Pulse_Elaborate_Pure.elab_term b.Pulse_Syntax_Base.binder_ty in
              let ppname =
                (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name in
              let body1 =
                elab_st_typing
                  (Pulse_Typing.extend x
                     (FStar_Pervasives.Inl (b.Pulse_Syntax_Base.binder_ty))
                     uu___)
                  (Pulse_Syntax_Naming.open_st_term_nv body
                     ((b.Pulse_Syntax_Base.binder_ppname), x)) _c body_typing in
              Pulse_Reflection_Util.mk_abs_with_name ppname ty
                (Pulse_Elaborate_Pure.elab_qual qual)
                (FStar_Reflection_Typing.close_term body1 x)
          | Pulse_Typing.T_STApp
              (uu___, head, _formal, qual, _res, arg, head_typing,
               arg_typing)
              ->
              let head1 = Pulse_Elaborate_Pure.elab_term head in
              let arg1 = Pulse_Elaborate_Pure.elab_term arg in
              FStar_Reflection_Derived.mk_app head1
                [(arg1, (Pulse_Elaborate_Pure.elab_qual qual))]
          | Pulse_Typing.T_Return
              (uu___, c1, use_eq, u, ty, t1, post, uu___1, uu___2, uu___3,
               uu___4)
              ->
              let ru = u in
              let rty = Pulse_Elaborate_Pure.elab_term ty in
              let rt = Pulse_Elaborate_Pure.elab_term t1 in
              let rp = Pulse_Elaborate_Pure.elab_term post in
              let rp1 =
                Pulse_Reflection_Util.mk_abs rty
                  FStar_Reflection_Data.Q_Explicit rp in
              (match (c1, use_eq) with
               | (Pulse_Syntax_Base.STT, true) ->
                   Pulse_Reflection_Util.mk_stt_return ru rty rt rp1
               | (Pulse_Syntax_Base.STT, false) ->
                   Pulse_Reflection_Util.mk_stt_return_noeq ru rty rt rp1
               | (Pulse_Syntax_Base.STT_Atomic, true) ->
                   Pulse_Reflection_Util.mk_stt_atomic_return ru rty rt rp1
               | (Pulse_Syntax_Base.STT_Atomic, false) ->
                   Pulse_Reflection_Util.mk_stt_atomic_return_noeq ru rty rt
                     rp1
               | (Pulse_Syntax_Base.STT_Ghost, true) ->
                   Pulse_Reflection_Util.mk_stt_ghost_return ru rty rt rp1
               | (Pulse_Syntax_Base.STT_Ghost, false) ->
                   Pulse_Reflection_Util.mk_stt_ghost_return_noeq ru rty rt
                     rp1)
          | Pulse_Typing.T_Bind
              (uu___, e1, e2, c1, c2, b, x, c3, e1_typing, t_typing,
               e2_typing, bc)
              ->
              let e11 = elab_st_typing uu___ e1 c1 e1_typing in
              let e21 =
                elab_st_typing
                  (Pulse_Typing.extend x
                     (FStar_Pervasives.Inl (Pulse_Syntax_Base.comp_res c1))
                     uu___)
                  (Pulse_Syntax_Naming.open_st_term_nv e2
                     ((b.Pulse_Syntax_Base.binder_ppname), x)) c2 e2_typing in
              let ty1 =
                Pulse_Elaborate_Pure.elab_term
                  (Pulse_Syntax_Base.comp_res c1) in
              elab_bind uu___ x c1 c2 c3 bc e11
                (Pulse_Reflection_Util.mk_abs_with_name
                   (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name
                   ty1 FStar_Reflection_Data.Q_Explicit
                   (FStar_Reflection_Typing.close_term e21 x))
          | Pulse_Typing.T_TotBind
              (uu___, e1, e2, t1, uu___1, x, uu___2, e2_typing) ->
              let re1 = Pulse_Elaborate_Pure.elab_term e1 in
              let rt1 = Pulse_Elaborate_Pure.elab_term t1 in
              let re2 =
                elab_st_typing
                  (Pulse_Typing.extend x (FStar_Pervasives.Inl t1) uu___)
                  (Pulse_Syntax_Naming.open_st_term_nv e2
                     (Pulse_Syntax_Base.v_as_nv x)) uu___1 e2_typing in
              FStar_Reflection_Typing.mk_let
                FStar_Reflection_Typing.pp_name_default re1 rt1
                (FStar_Reflection_Typing.close_term re2 x)
          | Pulse_Typing.T_Frame
              (uu___, uu___1, c1, frame, _frame_typing, e_typing) ->
              let e = elab_st_typing uu___ uu___1 c1 e_typing in
              elab_frame c1 frame e
          | Pulse_Typing.T_Equiv (uu___, uu___1, c1, c2, e_typing, uu___2) ->
              let e = elab_st_typing uu___ uu___1 c1 e_typing in
              elab_sub c1 c2 e
          | Pulse_Typing.T_Lift (uu___, uu___1, c1, c2, e_typing, lc) ->
              let e = elab_st_typing uu___ uu___1 c1 e_typing in
              elab_lift uu___ c1 c2 lc e
          | Pulse_Typing.T_If
              (uu___, b, uu___1, uu___2, uu___3, uu___4, uu___5, uu___6,
               e1_typing, e2_typing, _c_typing)
              ->
              let rb = Pulse_Elaborate_Pure.elab_term b in
              let re1 =
                elab_st_typing
                  (Pulse_Typing.extend uu___5
                     (FStar_Pervasives.Inl
                        (Pulse_Typing.mk_eq2 Pulse_Syntax_Pure.u0
                           Pulse_Typing.tm_bool b Pulse_Typing.tm_true))
                     uu___) uu___1 uu___3 e1_typing in
              let re2 =
                elab_st_typing
                  (Pulse_Typing.extend uu___5
                     (FStar_Pervasives.Inl
                        (Pulse_Typing.mk_eq2 Pulse_Syntax_Pure.u0
                           Pulse_Typing.tm_bool b Pulse_Typing.tm_false))
                     uu___) uu___2 uu___3 e2_typing in
              FStar_Reflection_Typing.mk_if rb re1 re2
          | Pulse_Typing.T_IntroPure (uu___, p, uu___1, uu___2) ->
              let head =
                Pulse_Syntax_Pure.tm_pureapp
                  (Pulse_Syntax_Pure.tm_fvar
                     (Pulse_Syntax_Base.as_fv
                        (Pulse_Reflection_Util.mk_steel_wrapper_lid
                           "intro_pure"))) FStar_Pervasives_Native.None p in
              let arg =
                FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_Const
                     FStar_Reflection_Data.C_Unit) in
              FStar_Reflection_Derived.mk_app
                (Pulse_Elaborate_Pure.elab_term head)
                [(arg,
                   (Pulse_Elaborate_Pure.elab_qual
                      FStar_Pervasives_Native.None))]
          | Pulse_Typing.T_ElimExists
              (uu___, u, t1, p, uu___1, d_t, d_exists) ->
              let ru = u in
              let rt = Pulse_Elaborate_Pure.elab_term t1 in
              let rp = Pulse_Elaborate_Pure.elab_term p in
              Pulse_Reflection_Util.mk_elim_exists ru rt
                (Pulse_Reflection_Util.mk_abs rt
                   FStar_Reflection_Data.Q_Explicit rp)
          | Pulse_Typing.T_IntroExists
              (uu___, u, t1, p, e, uu___1, uu___2, uu___3) ->
              let ru = u in
              let rt = Pulse_Elaborate_Pure.elab_term t1 in
              let rp = Pulse_Elaborate_Pure.elab_term p in
              let re = Pulse_Elaborate_Pure.elab_term e in
              Pulse_Reflection_Util.mk_intro_exists ru rt
                (Pulse_Reflection_Util.mk_abs rt
                   FStar_Reflection_Data.Q_Explicit rp) re
          | Pulse_Typing.T_IntroExistsErased
              (uu___, u, t1, p, e, uu___1, uu___2, uu___3) ->
              let ru = u in
              let rt = Pulse_Elaborate_Pure.elab_term t1 in
              let rp = Pulse_Elaborate_Pure.elab_term p in
              let re = Pulse_Elaborate_Pure.elab_term e in
              Pulse_Reflection_Util.mk_intro_exists_erased ru rt
                (Pulse_Reflection_Util.mk_abs rt
                   FStar_Reflection_Data.Q_Explicit rp) re
          | Pulse_Typing.T_While
              (uu___, inv, uu___1, uu___2, uu___3, cond_typing, body_typing)
              ->
              let inv1 = Pulse_Elaborate_Pure.elab_term inv in
              let cond =
                elab_st_typing uu___ uu___1
                  (Pulse_Typing.comp_while_cond inv) cond_typing in
              let body =
                elab_st_typing uu___ uu___2
                  (Pulse_Typing.comp_while_body inv) body_typing in
              Pulse_Reflection_Util.mk_while
                (Pulse_Reflection_Util.mk_abs Pulse_Reflection_Util.bool_tm
                   FStar_Reflection_Data.Q_Explicit inv1) cond body
          | Pulse_Typing.T_Par
              (uu___, eL, cL, eR, cR, uu___1, uu___2, uu___3, eL_typing,
               eR_typing)
              ->
              let ru = Pulse_Syntax_Base.comp_u cL in
              let raL =
                Pulse_Elaborate_Pure.elab_term
                  (Pulse_Syntax_Base.comp_res cL) in
              let raR =
                Pulse_Elaborate_Pure.elab_term
                  (Pulse_Syntax_Base.comp_res cR) in
              let rpreL =
                Pulse_Elaborate_Pure.elab_term
                  (Pulse_Syntax_Base.comp_pre cL) in
              let rpostL =
                Pulse_Elaborate_Pure.elab_term
                  (Pulse_Syntax_Base.comp_post cL) in
              let rpreR =
                Pulse_Elaborate_Pure.elab_term
                  (Pulse_Syntax_Base.comp_pre cR) in
              let rpostR =
                Pulse_Elaborate_Pure.elab_term
                  (Pulse_Syntax_Base.comp_post cR) in
              let reL = elab_st_typing uu___ eL cL eL_typing in
              let reR = elab_st_typing uu___ eR cR eR_typing in
              Pulse_Reflection_Util.mk_par ru raL raR rpreL
                (Pulse_Reflection_Util.mk_abs raL
                   FStar_Reflection_Data.Q_Explicit rpostL) rpreR
                (Pulse_Reflection_Util.mk_abs raR
                   FStar_Reflection_Data.Q_Explicit rpostR) reL reR
          | Pulse_Typing.T_Rewrite (uu___, p, q, uu___1, uu___2) ->
              let rp = Pulse_Elaborate_Pure.elab_term p in
              let rq = Pulse_Elaborate_Pure.elab_term q in
              Pulse_Reflection_Util.mk_rewrite rp rq
          | Pulse_Typing.T_WithLocal
              (uu___, init, uu___1, init_t, c1, x, uu___2, uu___3, uu___4,
               body_typing)
              ->
              let rret_u = Pulse_Syntax_Base.comp_u c1 in
              let ra = Pulse_Elaborate_Pure.elab_term init_t in
              let rinit = Pulse_Elaborate_Pure.elab_term init in
              let rret_t =
                Pulse_Elaborate_Pure.elab_term
                  (Pulse_Syntax_Base.comp_res c1) in
              let rpre =
                Pulse_Elaborate_Pure.elab_term
                  (Pulse_Syntax_Base.comp_pre c1) in
              let rpost =
                Pulse_Reflection_Util.mk_abs rret_t
                  FStar_Reflection_Data.Q_Explicit
                  (Pulse_Elaborate_Pure.elab_term
                     (Pulse_Syntax_Base.comp_post c1)) in
              let rbody =
                elab_st_typing
                  (Pulse_Typing.extend x
                     (FStar_Pervasives.Inl (Pulse_Typing.mk_ref init_t))
                     uu___)
                  (Pulse_Syntax_Naming.open_st_term_nv uu___1
                     (Pulse_Syntax_Base.v_as_nv x))
                  (Pulse_Typing.comp_withlocal_body x init_t init c1)
                  body_typing in
              let rbody1 = FStar_Reflection_Typing.close_term rbody x in
              let rbody2 =
                Pulse_Reflection_Util.mk_abs
                  (Pulse_Reflection_Util.mk_ref ra)
                  FStar_Reflection_Data.Q_Explicit rbody1 in
              Pulse_Reflection_Util.mk_withlocal rret_u ra rinit rpre rret_t
                rpost rbody2
          | Pulse_Typing.T_Admit
              (uu___,
               { Pulse_Syntax_Base.u = u; Pulse_Syntax_Base.res = res;
                 Pulse_Syntax_Base.pre = pre;
                 Pulse_Syntax_Base.post = post;_},
               c1, uu___1)
              ->
              let ru = u in
              let rres = Pulse_Elaborate_Pure.elab_term res in
              let rpre = Pulse_Elaborate_Pure.elab_term pre in
              let rpost = Pulse_Elaborate_Pure.elab_term post in
              let rpost1 =
                Pulse_Reflection_Util.mk_abs rres
                  FStar_Reflection_Data.Q_Explicit rpost in
              (match c1 with
               | Pulse_Syntax_Base.STT ->
                   Pulse_Reflection_Util.mk_stt_admit ru rres rpre rpost1
               | Pulse_Syntax_Base.STT_Atomic ->
                   Pulse_Reflection_Util.mk_stt_atomic_admit ru rres rpre
                     rpost1
               | Pulse_Syntax_Base.STT_Ghost ->
                   Pulse_Reflection_Util.mk_stt_ghost_admit ru rres rpre
                     rpost1)