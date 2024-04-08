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
        let ty = Pulse_Syntax_Base.comp_res c in
        let pre = Pulse_Syntax_Base.comp_pre c in
        let post = Pulse_Syntax_Base.comp_post c in
        if Pulse_Syntax_Base.uu___is_C_ST c
        then
          Pulse_Reflection_Util.mk_frame_stt u ty pre
            (Pulse_Reflection_Util.mk_abs ty
               FStar_Reflection_V2_Data.Q_Explicit post) frame e
        else
          if Pulse_Syntax_Base.uu___is_C_STAtomic c
          then
            (let opened = Pulse_Syntax_Base.comp_inames c in
             Pulse_Reflection_Util.mk_frame_stt_atomic u ty opened pre
               (Pulse_Reflection_Util.mk_abs ty
                  FStar_Reflection_V2_Data.Q_Explicit post) frame e)
          else
            Pulse_Reflection_Util.mk_frame_stt_ghost u ty pre
              (Pulse_Reflection_Util.mk_abs ty
                 FStar_Reflection_V2_Data.Q_Explicit post) frame e
let (elab_sub :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.comp_st ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun c1 ->
    fun c2 ->
      fun e ->
        let ty = Pulse_Syntax_Base.comp_res c1 in
        let u = Pulse_Syntax_Base.comp_u c1 in
        let pre1 = Pulse_Syntax_Base.comp_pre c1 in
        let pre2 = Pulse_Syntax_Base.comp_pre c2 in
        let post1 =
          Pulse_Reflection_Util.mk_abs ty FStar_Reflection_V2_Data.Q_Explicit
            (Pulse_Syntax_Base.comp_post c1) in
        let post2 =
          Pulse_Reflection_Util.mk_abs ty FStar_Reflection_V2_Data.Q_Explicit
            (Pulse_Syntax_Base.comp_post c2) in
        if Pulse_Syntax_Base.uu___is_C_ST c1
        then Pulse_Reflection_Util.mk_sub_stt u ty pre1 pre2 post1 post2 e
        else
          if Pulse_Syntax_Base.uu___is_C_STAtomic c1
          then
            (let opened = Pulse_Syntax_Base.comp_inames c1 in
             Pulse_Reflection_Util.mk_sub_stt_atomic u ty opened pre1 pre2
               post1 post2 e)
          else
            Pulse_Reflection_Util.mk_sub_stt_ghost u ty pre1 pre2 post1 post2
              e
let (elab_bind :
  Pulse_Typing_Env.env ->
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
                  let t1 = Pulse_Syntax_Base.comp_res c1 in
                  let t2 = Pulse_Syntax_Base.comp_res c2 in
                  match c1 with
                  | Pulse_Syntax_Base.C_ST uu___ ->
                      Pulse_Reflection_Util.mk_bind_stt
                        (Pulse_Syntax_Base.comp_u c1)
                        (Pulse_Syntax_Base.comp_u c2) t1 t2
                        (Pulse_Syntax_Base.comp_pre c1)
                        (Pulse_Reflection_Util.mk_abs t1
                           FStar_Reflection_V2_Data.Q_Explicit
                           (Pulse_Syntax_Base.comp_post c1))
                        (Pulse_Reflection_Util.mk_abs t2
                           FStar_Reflection_V2_Data.Q_Explicit
                           (Pulse_Syntax_Base.comp_post c2)) e1 e2
                  | Pulse_Syntax_Base.C_STGhost (inames, uu___) ->
                      Pulse_Reflection_Util.mk_bind_ghost
                        (Pulse_Syntax_Base.comp_u c1)
                        (Pulse_Syntax_Base.comp_u c2) t1 t2 inames
                        (Pulse_Syntax_Base.comp_pre c1)
                        (Pulse_Reflection_Util.mk_abs t1
                           FStar_Reflection_V2_Data.Q_Explicit
                           (Pulse_Syntax_Base.comp_post c1))
                        (Pulse_Reflection_Util.mk_abs t2
                           FStar_Reflection_V2_Data.Q_Explicit
                           (Pulse_Syntax_Base.comp_post c2)) e1 e2
                  | Pulse_Syntax_Base.C_STAtomic (inames, obs1, uu___) ->
                      let uu___1 = c2 in
                      (match uu___1 with
                       | Pulse_Syntax_Base.C_STAtomic (uu___2, obs2, uu___3)
                           ->
                           Pulse_Reflection_Util.mk_bind_atomic
                             (Pulse_Syntax_Base.comp_u c1)
                             (Pulse_Syntax_Base.comp_u c2)
                             (Pulse_Elaborate_Pure.elab_observability obs1)
                             (Pulse_Elaborate_Pure.elab_observability obs2)
                             (Pulse_Syntax_Base.comp_inames c1) t1 t2
                             (Pulse_Syntax_Base.comp_pre c1)
                             (Pulse_Reflection_Util.mk_abs t1
                                FStar_Reflection_V2_Data.Q_Explicit
                                (Pulse_Syntax_Base.comp_post c1))
                             (Pulse_Reflection_Util.mk_abs t2
                                FStar_Reflection_V2_Data.Q_Explicit
                                (Pulse_Syntax_Base.comp_post c2)) e1 e2)
let (elab_lift :
  Pulse_Typing_Env.env ->
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
                let t = Pulse_Syntax_Base.comp_res c1 in
                Pulse_Reflection_Util.mk_lift_atomic_stt
                  (Pulse_Syntax_Base.comp_u c1)
                  (Pulse_Syntax_Base.comp_res c1) t
                  (Pulse_Reflection_Util.mk_abs t
                     FStar_Reflection_V2_Data.Q_Explicit
                     (Pulse_Syntax_Base.comp_post c1)) e
            | Pulse_Typing.Lift_Observability (uu___, c, o2) ->
                let t = Pulse_Syntax_Base.comp_res c1 in
                Pulse_Reflection_Util.mk_lift_observability
                  (Pulse_Syntax_Base.comp_u c1)
                  (Pulse_Elaborate_Pure.elab_observability
                     (Pulse_Syntax_Base.__proj__C_STAtomic__item__obs c))
                  (Pulse_Elaborate_Pure.elab_observability o2)
                  (Pulse_Syntax_Base.comp_inames c1) t
                  (Pulse_Syntax_Base.comp_pre c1)
                  (Pulse_Reflection_Util.mk_abs t
                     FStar_Reflection_V2_Data.Q_Explicit
                     (Pulse_Syntax_Base.comp_post c1)) e
            | Pulse_Typing.Lift_Ghost_Neutral
                (uu___, uu___1, Prims.Mkdtuple2 (reveal_a, reveal_a_typing))
                ->
                let t = Pulse_Syntax_Base.comp_res c1 in
                Pulse_Reflection_Util.mk_lift_ghost_neutral
                  (Pulse_Syntax_Base.comp_u c1) t
                  (Pulse_Syntax_Base.comp_pre c1)
                  (Pulse_Reflection_Util.mk_abs t
                     FStar_Reflection_V2_Data.Q_Explicit
                     (Pulse_Syntax_Base.comp_post c1)) e reveal_a
            | Pulse_Typing.Lift_Neutral_Ghost (uu___, c) ->
                let t = Pulse_Syntax_Base.comp_res c1 in
                Pulse_Reflection_Util.mk_lift_neutral_ghost
                  (Pulse_Syntax_Base.comp_u c1) t
                  (Pulse_Syntax_Base.comp_pre c1)
                  (Pulse_Reflection_Util.mk_abs t
                     FStar_Reflection_V2_Data.Q_Explicit
                     (Pulse_Syntax_Base.comp_post c1)) e
let (intro_pure_tm : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term) =
  fun p ->
    Pulse_Typing.wtag
      (FStar_Pervasives_Native.Some Pulse_Syntax_Base.STT_Ghost)
      (Pulse_Syntax_Base.Tm_STApp
         {
           Pulse_Syntax_Base.head =
             (Pulse_Syntax_Pure.tm_pureapp
                (Pulse_Syntax_Pure.tm_fvar
                   (Pulse_Syntax_Base.as_fv
                      (Pulse_Reflection_Util.mk_pulse_lib_core_lid
                         "intro_pure"))) FStar_Pervasives_Native.None p);
           Pulse_Syntax_Base.arg_qual = FStar_Pervasives_Native.None;
           Pulse_Syntax_Base.arg =
             (Pulse_Syntax_Pure.wr
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_Const
                      FStar_Reflection_V2_Data.C_Unit)) FStar_Range.range_0)
         })
let (simple_arr :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t1 ->
    fun t2 ->
      let b =
        FStar_Reflection_V2_Builtins.pack_binder
          {
            FStar_Reflection_V2_Data.sort2 = t1;
            FStar_Reflection_V2_Data.qual =
              FStar_Reflection_V2_Data.Q_Explicit;
            FStar_Reflection_V2_Data.attrs = [];
            FStar_Reflection_V2_Data.ppname2 = (FStar_Sealed.seal "x")
          } in
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_Arrow
           (b,
             (FStar_Reflection_V2_Builtins.pack_comp
                (FStar_Reflection_V2_Data.C_Total t2))))
let (elab_st_sub :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_sub ->
          (FStar_Reflection_Types.term,
            (unit, unit, unit) FStar_Reflection_Typing.tot_typing)
            Prims.dtuple2)
  =
  fun g ->
    fun c1 -> fun c2 -> fun d_sub -> Pulse_RuntimeUtils.magic_s "elab_st_sub"
let rec (elab_st_typing :
  Pulse_Typing_Env.env ->
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
              let ty = b.Pulse_Syntax_Base.binder_ty in
              let ppname =
                (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name in
              let body1 =
                elab_st_typing
                  (Pulse_Typing_Env.push_binding uu___ x
                     Pulse_Syntax_Base.ppname_default
                     b.Pulse_Syntax_Base.binder_ty)
                  (Pulse_Syntax_Naming.open_st_term_nv body
                     ((b.Pulse_Syntax_Base.binder_ppname), x)) _c body_typing in
              Pulse_Reflection_Util.mk_abs_with_name ppname ty
                (Pulse_Elaborate_Pure.elab_qual qual)
                (FStar_Reflection_Typing.close_term body1 x)
          | Pulse_Typing.T_STApp
              (uu___, head, uu___1, qual, uu___2, arg, uu___3, uu___4) ->
              FStar_Reflection_V2_Derived.mk_app head
                [(arg, (Pulse_Elaborate_Pure.elab_qual qual))]
          | Pulse_Typing.T_STGhostApp
              (uu___, head, uu___1, qual, uu___2, arg, uu___3, uu___4,
               uu___5, uu___6)
              ->
              FStar_Reflection_V2_Derived.mk_app head
                [(arg, (Pulse_Elaborate_Pure.elab_qual qual))]
          | Pulse_Typing.T_Return
              (uu___, c1, use_eq, u, ty, t1, post, uu___1, uu___2, uu___3,
               uu___4)
              ->
              let rp =
                Pulse_Reflection_Util.mk_abs ty
                  FStar_Reflection_V2_Data.Q_Explicit post in
              (match (c1, use_eq) with
               | (Pulse_Syntax_Base.STT, true) ->
                   Pulse_Reflection_Util.mk_stt_return u ty t1 rp
               | (Pulse_Syntax_Base.STT, false) ->
                   Pulse_Reflection_Util.mk_stt_return_noeq u ty t1 rp
               | (Pulse_Syntax_Base.STT_Atomic, true) ->
                   Pulse_Reflection_Util.mk_stt_atomic_return u ty t1 rp
               | (Pulse_Syntax_Base.STT_Atomic, false) ->
                   Pulse_Reflection_Util.mk_stt_atomic_return_noeq u ty t1 rp
               | (Pulse_Syntax_Base.STT_Ghost, true) ->
                   Pulse_Reflection_Util.mk_stt_ghost_return u ty t1 rp
               | (Pulse_Syntax_Base.STT_Ghost, false) ->
                   Pulse_Reflection_Util.mk_stt_ghost_return_noeq u ty t1 rp)
          | Pulse_Typing.T_Bind
              (uu___, e1, e2, c1, c2, b, x, c3, e1_typing, t_typing,
               e2_typing, bc)
              ->
              let e11 = elab_st_typing uu___ e1 c1 e1_typing in
              let e21 =
                elab_st_typing
                  (Pulse_Typing_Env.push_binding uu___ x
                     Pulse_Syntax_Base.ppname_default
                     (Pulse_Syntax_Base.comp_res c1))
                  (Pulse_Syntax_Naming.open_st_term_nv e2
                     ((b.Pulse_Syntax_Base.binder_ppname), x)) c2 e2_typing in
              let ty1 = Pulse_Syntax_Base.comp_res c1 in
              elab_bind uu___ x c1 c2 c3 bc e11
                (Pulse_Reflection_Util.mk_abs_with_name
                   (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name
                   ty1 FStar_Reflection_V2_Data.Q_Explicit
                   (FStar_Reflection_Typing.close_term e21 x))
          | Pulse_Typing.T_BindFn
              (uu___, uu___1, uu___2, c1, c2, b, x, e1_typing, _u, t_typing,
               e2_typing, c2_typing)
              ->
              let e1 = elab_st_typing uu___ uu___1 c1 e1_typing in
              let e2 =
                elab_st_typing
                  (Pulse_Typing_Env.push_binding uu___ x
                     Pulse_Syntax_Base.ppname_default
                     (Pulse_Syntax_Base.comp_res c1))
                  (Pulse_Syntax_Naming.open_st_term_nv uu___2
                     ((b.Pulse_Syntax_Base.binder_ppname), x)) c2 e2_typing in
              let ty1 = Pulse_Syntax_Base.comp_res c1 in
              FStar_Reflection_Typing.mk_let
                FStar_Reflection_Typing.pp_name_default e1 ty1
                (FStar_Reflection_Typing.close_term e2 x)
          | Pulse_Typing.T_Frame
              (uu___, uu___1, c1, frame, _frame_typing, e_typing) ->
              let e = elab_st_typing uu___ uu___1 c1 e_typing in
              elab_frame c1 frame e
          | Pulse_Typing.T_Equiv
              (uu___, uu___1, c1, c2, e_typing, Pulse_Typing.ST_TotEquiv
               (uu___2, uu___3, uu___4, uu___5, uu___6, uu___7))
              -> let e = elab_st_typing uu___ uu___1 c1 e_typing in e
          | Pulse_Typing.T_Equiv (uu___, uu___1, c1, c2, e_typing, uu___2) ->
              let e = elab_st_typing uu___ uu___1 c1 e_typing in
              elab_sub c1 c2 e
          | Pulse_Typing.T_Sub (uu___, uu___1, c1, c2, e_typing, d_sub) ->
              let e = elab_st_typing uu___ uu___1 c1 e_typing in
              let uu___2 = elab_st_sub uu___ c1 c2 d_sub in
              (match uu___2 with
               | Prims.Mkdtuple2 (coercion, uu___3) ->
                   FStar_Reflection_V2_Derived.mk_e_app coercion [e])
          | Pulse_Typing.T_Lift (uu___, uu___1, c1, c2, e_typing, lc) ->
              let e = elab_st_typing uu___ uu___1 c1 e_typing in
              elab_lift uu___ c1 c2 lc e
          | Pulse_Typing.T_If
              (uu___, b, uu___1, uu___2, uu___3, uu___4, uu___5, e1_typing,
               e2_typing, _c_typing)
              ->
              let re1 =
                elab_st_typing
                  (Pulse_Typing_Env.push_binding uu___ uu___4
                     Pulse_Syntax_Base.ppname_default
                     (Pulse_Typing.mk_eq2 Pulse_Syntax_Pure.u0
                        Pulse_Typing.tm_bool b Pulse_Typing.tm_true)) uu___1
                  uu___3 e1_typing in
              let re2 =
                elab_st_typing
                  (Pulse_Typing_Env.push_binding uu___ uu___4
                     Pulse_Syntax_Base.ppname_default
                     (Pulse_Typing.mk_eq2 Pulse_Syntax_Pure.u0
                        Pulse_Typing.tm_bool b Pulse_Typing.tm_false)) uu___2
                  uu___3 e2_typing in
              FStar_Reflection_Typing.mk_if b re1 re2
          | Pulse_Typing.T_Match
              (uu___, uu___1, uu___2, sc, uu___3, uu___4, uu___5, uu___6,
               uu___7, brty, uu___8)
              ->
              let brs =
                elab_branches uu___ uu___5 uu___1 uu___2 sc uu___7 brty in
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_Match
                   (sc, FStar_Pervasives_Native.None, brs))
          | Pulse_Typing.T_IntroPure (uu___, p, uu___1, uu___2) ->
              let head =
                Pulse_Syntax_Pure.tm_pureapp
                  (Pulse_Syntax_Pure.tm_fvar
                     (Pulse_Syntax_Base.as_fv
                        (Pulse_Reflection_Util.mk_pulse_lib_core_lid
                           "intro_pure"))) FStar_Pervasives_Native.None p in
              let arg =
                FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_Const
                     FStar_Reflection_V2_Data.C_Unit) in
              FStar_Reflection_V2_Derived.mk_app head
                [(arg,
                   (Pulse_Elaborate_Pure.elab_qual
                      FStar_Pervasives_Native.None))]
          | Pulse_Typing.T_ElimExists
              (uu___, u, t1, p, uu___1, d_t, d_exists) ->
              Pulse_Reflection_Util.mk_elim_exists u t1
                (Pulse_Reflection_Util.mk_abs t1
                   FStar_Reflection_V2_Data.Q_Explicit p)
          | Pulse_Typing.T_IntroExists
              (uu___, u, b, p, e, uu___1, uu___2, uu___3) ->
              let rt = b.Pulse_Syntax_Base.binder_ty in
              Pulse_Reflection_Util.mk_intro_exists u rt
                (Pulse_Reflection_Util.mk_abs rt
                   FStar_Reflection_V2_Data.Q_Explicit p) e
          | Pulse_Typing.T_While
              (uu___, inv, uu___1, uu___2, uu___3, cond_typing, body_typing)
              ->
              let cond =
                elab_st_typing uu___ uu___1
                  (Pulse_Typing.comp_while_cond
                     Pulse_Syntax_Base.ppname_default inv) cond_typing in
              let body =
                elab_st_typing uu___ uu___2
                  (Pulse_Typing.comp_while_body
                     Pulse_Syntax_Base.ppname_default inv) body_typing in
              Pulse_Reflection_Util.mk_while
                (Pulse_Reflection_Util.mk_abs Pulse_Reflection_Util.bool_tm
                   FStar_Reflection_V2_Data.Q_Explicit inv) cond body
          | Pulse_Typing.T_Par
              (uu___, eL, cL, eR, cR, uu___1, uu___2, uu___3, eL_typing,
               eR_typing)
              ->
              let ru = Pulse_Syntax_Base.comp_u cL in
              let raL = Pulse_Syntax_Base.comp_res cL in
              let raR = Pulse_Syntax_Base.comp_res cR in
              let rpreL = Pulse_Syntax_Base.comp_pre cL in
              let rpostL = Pulse_Syntax_Base.comp_post cL in
              let rpreR = Pulse_Syntax_Base.comp_pre cR in
              let rpostR = Pulse_Syntax_Base.comp_post cR in
              let reL = elab_st_typing uu___ eL cL eL_typing in
              let reR = elab_st_typing uu___ eR cR eR_typing in
              Pulse_Reflection_Util.mk_par ru raL raR rpreL
                (Pulse_Reflection_Util.mk_abs raL
                   FStar_Reflection_V2_Data.Q_Explicit rpostL) rpreR
                (Pulse_Reflection_Util.mk_abs raR
                   FStar_Reflection_V2_Data.Q_Explicit rpostR) reL reR
          | Pulse_Typing.T_Rewrite (uu___, p, q, uu___1, uu___2) ->
              Pulse_Reflection_Util.mk_rewrite p q
          | Pulse_Typing.T_WithLocal
              (uu___, uu___1, init, uu___2, init_t, c1, x, uu___3, uu___4,
               uu___5, body_typing)
              ->
              let rret_u = Pulse_Syntax_Base.comp_u c1 in
              let rret_t = Pulse_Syntax_Base.comp_res c1 in
              let rpre = Pulse_Syntax_Base.comp_pre c1 in
              let rpost =
                Pulse_Reflection_Util.mk_abs rret_t
                  FStar_Reflection_V2_Data.Q_Explicit
                  (Pulse_Syntax_Base.comp_post c1) in
              let rbody =
                elab_st_typing
                  (Pulse_Typing_Env.push_binding uu___ x
                     Pulse_Syntax_Base.ppname_default
                     (Pulse_Typing.mk_ref init_t))
                  (Pulse_Syntax_Naming.open_st_term_nv uu___2
                     (Pulse_Syntax_Base.v_as_nv x))
                  (Pulse_Typing.comp_withlocal_body x init_t init c1)
                  body_typing in
              let rbody1 = FStar_Reflection_Typing.close_term rbody x in
              let rbody2 =
                Pulse_Reflection_Util.mk_abs
                  (Pulse_Reflection_Util.mk_ref init_t)
                  FStar_Reflection_V2_Data.Q_Explicit rbody1 in
              Pulse_Reflection_Util.mk_withlocal rret_u init_t init rpre
                rret_t rpost rbody2
          | Pulse_Typing.T_WithLocalArray
              (uu___, uu___1, init, len, uu___2, init_t, c1, x, uu___3,
               uu___4, uu___5, uu___6, body_typing)
              ->
              let rret_u = Pulse_Syntax_Base.comp_u c1 in
              let rret_t = Pulse_Syntax_Base.comp_res c1 in
              let rpre = Pulse_Syntax_Base.comp_pre c1 in
              let rpost =
                Pulse_Reflection_Util.mk_abs rret_t
                  FStar_Reflection_V2_Data.Q_Explicit
                  (Pulse_Syntax_Base.comp_post c1) in
              let rbody =
                elab_st_typing
                  (Pulse_Typing_Env.push_binding uu___ x
                     Pulse_Syntax_Base.ppname_default
                     (Pulse_Typing.mk_array init_t))
                  (Pulse_Syntax_Naming.open_st_term_nv uu___2
                     (Pulse_Syntax_Base.v_as_nv x))
                  (Pulse_Typing.comp_withlocal_array_body x init_t init len
                     c1) body_typing in
              let rbody1 = FStar_Reflection_Typing.close_term rbody x in
              let rbody2 =
                Pulse_Reflection_Util.mk_abs
                  (Pulse_Reflection_Util.mk_array init_t)
                  FStar_Reflection_V2_Data.Q_Explicit rbody1 in
              Pulse_Reflection_Util.mk_withlocalarray rret_u init_t init len
                rpre rret_t rpost rbody2
          | Pulse_Typing.T_Admit
              (uu___,
               { Pulse_Syntax_Base.u = u; Pulse_Syntax_Base.res = res;
                 Pulse_Syntax_Base.pre = pre;
                 Pulse_Syntax_Base.post = post;_},
               c1, uu___1)
              ->
              let ru = u in
              let rpost =
                Pulse_Reflection_Util.mk_abs res
                  FStar_Reflection_V2_Data.Q_Explicit post in
              (match c1 with
               | Pulse_Syntax_Base.STT ->
                   Pulse_Reflection_Util.mk_stt_admit ru res pre rpost
               | Pulse_Syntax_Base.STT_Atomic ->
                   Pulse_Reflection_Util.mk_stt_atomic_admit ru res pre rpost
               | Pulse_Syntax_Base.STT_Ghost ->
                   Pulse_Reflection_Util.mk_stt_ghost_admit ru res pre rpost)
          | Pulse_Typing.T_Unreachable
              (uu___, uu___1, uu___2, uu___3, uu___4) ->
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_Const
                   (FStar_Reflection_V2_Data.C_String
                      "IOU: elab_st_typing of T_Unreachable"))
          | Pulse_Typing.T_WithInv
              (uu___, uu___1, uu___2, uu___3, uu___4, uu___5, uu___6, uu___7,
               uu___8)
              ->
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_Const
                   (FStar_Reflection_V2_Data.C_String
                      "IOU: elab_st_typing of T_WithInv"))
and (elab_br :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.typ ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.pattern ->
              Pulse_Syntax_Base.st_term ->
                (unit, unit, unit, unit, unit, unit, unit)
                  Pulse_Typing.br_typing -> FStar_Reflection_V2_Data.branch)
  =
  fun g ->
    fun c ->
      fun sc_u ->
        fun sc_ty ->
          fun sc ->
            fun p ->
              fun e ->
                fun d ->
                  let uu___ = d in
                  match uu___ with
                  | Pulse_Typing.TBR
                      (uu___1, uu___2, uu___3, uu___4, uu___5, uu___6,
                       uu___7, uu___8, bs, uu___9, uu___10, uu___11, ed)
                      ->
                      let e1 =
                        elab_st_typing
                          (Pulse_Typing_Env.push_binding
                             (Pulse_Typing.push_bindings uu___1
                                (FStar_List_Tot_Base.map
                                   Pulse_Typing.readback_binding uu___8))
                             uu___11
                             {
                               Pulse_Syntax_Base.name =
                                 (FStar_Sealed.seal "branch equality");
                               Pulse_Syntax_Base.range = FStar_Range.range_0
                             }
                             (Pulse_Typing.mk_sq_eq2 uu___2 uu___3 uu___4
                                (Pulse_Syntax_Pure.wr
                                   (FStar_Pervasives_Native.fst
                                      (FStar_Pervasives_Native.__proj__Some__item__v
                                         (FStar_Reflection_Typing.elaborate_pat
                                            (Pulse_Elaborate_Pure.elab_pat
                                               uu___6) uu___8)))
                                   FStar_Range.range_0))) uu___7 uu___5 ed in
                      ((Pulse_Elaborate_Pure.elab_pat p), e1)
and (elab_branches :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.typ ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.branch Prims.list ->
              (unit, unit, unit, unit, unit, unit) Pulse_Typing.brs_typing ->
                FStar_Reflection_V2_Data.branch Prims.list)
  =
  fun g ->
    fun c ->
      fun sc_u ->
        fun sc_ty ->
          fun sc ->
            fun brs ->
              fun d ->
                match d with
                | Pulse_Typing.TBRS_0 uu___ -> []
                | Pulse_Typing.TBRS_1 (uu___, p, e, bd, uu___1, d') ->
                    (elab_br g uu___ sc_u sc_ty sc p e bd) ::
                    (elab_branches g uu___ sc_u sc_ty sc uu___1 d')