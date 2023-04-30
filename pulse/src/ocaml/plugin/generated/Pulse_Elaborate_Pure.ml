open Prims
let rec (elab_universe :
  Pulse_Syntax.universe -> FStar_Reflection_Types.universe) =
  fun u ->
    match u with
    | Pulse_Syntax.U_unknown ->
        FStar_Reflection_Builtins.pack_universe FStar_Reflection_Data.Uv_Unk
    | Pulse_Syntax.U_zero ->
        FStar_Reflection_Builtins.pack_universe FStar_Reflection_Data.Uv_Zero
    | Pulse_Syntax.U_succ u1 ->
        FStar_Reflection_Builtins.pack_universe
          (FStar_Reflection_Data.Uv_Succ (elab_universe u1))
    | Pulse_Syntax.U_var x ->
        FStar_Reflection_Builtins.pack_universe
          (FStar_Reflection_Data.Uv_Name
             (x, FStar_Reflection_Typing_Builtins.dummy_range))
    | Pulse_Syntax.U_max (u1, u2) ->
        FStar_Reflection_Builtins.pack_universe
          (FStar_Reflection_Data.Uv_Max [elab_universe u1; elab_universe u2])
let op_let_Bang :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a -> 'b FStar_Pervasives_Native.option) ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun g ->
      match f with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x -> g x
let (elab_const : Pulse_Syntax.constant -> FStar_Reflection_Data.vconst) =
  fun c ->
    match c with
    | Pulse_Syntax.Unit -> FStar_Reflection_Data.C_Unit
    | Pulse_Syntax.Bool (true) -> FStar_Reflection_Data.C_True
    | Pulse_Syntax.Bool (false) -> FStar_Reflection_Data.C_False
    | Pulse_Syntax.Int i -> FStar_Reflection_Data.C_Int i
let (elab_qual :
  Pulse_Syntax.qualifier FStar_Pervasives_Native.option ->
    FStar_Reflection_Data.aqualv)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_Reflection_Data.Q_Explicit
    | FStar_Pervasives_Native.Some (Pulse_Syntax.Implicit) ->
        FStar_Reflection_Data.Q_Implicit
let rec (elab_term : Pulse_Syntax.term -> FStar_Reflection_Types.term) =
  fun top ->
    match top with
    | Pulse_Syntax.Tm_BVar bv ->
        let bv1 =
          FStar_Reflection_Builtins.pack_bv
            (FStar_Reflection_Typing.make_bv_with_name
               bv.Pulse_Syntax.bv_ppname bv.Pulse_Syntax.bv_index) in
        FStar_Reflection_Builtins.pack_ln (FStar_Reflection_Data.Tv_BVar bv1)
    | Pulse_Syntax.Tm_Var nm ->
        let bv =
          FStar_Reflection_Builtins.pack_bv
            (FStar_Reflection_Typing.make_bv_with_name
               nm.Pulse_Syntax.nm_ppname nm.Pulse_Syntax.nm_index) in
        FStar_Reflection_Builtins.pack_ln (FStar_Reflection_Data.Tv_Var bv)
    | Pulse_Syntax.Tm_FVar l ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv l))
    | Pulse_Syntax.Tm_UInst (l, us) ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_UInst
             ((FStar_Reflection_Builtins.pack_fv l),
               (FStar_List_Tot_Base.map elab_universe us)))
    | Pulse_Syntax.Tm_Constant c ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_Const (elab_const c))
    | Pulse_Syntax.Tm_Refine (b, phi) ->
        let ty = elab_term b.Pulse_Syntax.binder_ty in
        let phi1 = elab_term phi in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_Refine
             ((FStar_Reflection_Builtins.pack_bv
                 (FStar_Reflection_Typing.make_bv_with_name
                    b.Pulse_Syntax.binder_ppname Prims.int_zero)), ty, phi1))
    | Pulse_Syntax.Tm_PureApp (e1, q, e2) ->
        let e11 = elab_term e1 in
        let e21 = elab_term e2 in
        FStar_Reflection_Derived.mk_app e11 [(e21, (elab_qual q))]
    | Pulse_Syntax.Tm_Arrow (b, q, c) ->
        let ty = elab_term b.Pulse_Syntax.binder_ty in
        let c1 = elab_comp c in
        Pulse_Reflection_Util.mk_arrow_with_name b.Pulse_Syntax.binder_ppname
          (ty, (elab_qual q)) c1
    | Pulse_Syntax.Tm_Let (t, e1, e2) ->
        let t1 = elab_term t in
        let e11 = elab_term e1 in
        let e21 = elab_term e2 in
        let bv =
          FStar_Reflection_Builtins.pack_bv
            (FStar_Reflection_Typing.make_bv Prims.int_zero) in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_Let (false, [], bv, t1, e11, e21))
    | Pulse_Syntax.Tm_Type u ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_Type (elab_universe u))
    | Pulse_Syntax.Tm_VProp ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                Pulse_Reflection_Util.vprop_lid))
    | Pulse_Syntax.Tm_Emp ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv Pulse_Reflection_Util.emp_lid))
    | Pulse_Syntax.Tm_Pure p ->
        let p1 = elab_term p in
        let head =
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_FVar
               (FStar_Reflection_Builtins.pack_fv
                  Pulse_Reflection_Util.pure_lid)) in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             (head, (p1, FStar_Reflection_Data.Q_Explicit)))
    | Pulse_Syntax.Tm_Star (l, r) ->
        let l1 = elab_term l in
        let r1 = elab_term r in Pulse_Reflection_Util.mk_star l1 r1
    | Pulse_Syntax.Tm_ExistsSL (u, t, body, uu___) ->
        let u1 = elab_universe u in
        let t1 = elab_term t in
        let b = elab_term body in
        if Pulse_Syntax.uu___is_Tm_ExistsSL top
        then
          Pulse_Reflection_Util.mk_exists u1 t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
        else
          Pulse_Reflection_Util.mk_forall u1 t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
    | Pulse_Syntax.Tm_ForallSL (u, t, body) ->
        let u1 = elab_universe u in
        let t1 = elab_term t in
        let b = elab_term body in
        if Pulse_Syntax.uu___is_Tm_ExistsSL top
        then
          Pulse_Reflection_Util.mk_exists u1 t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
        else
          Pulse_Reflection_Util.mk_forall u1 t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
    | Pulse_Syntax.Tm_Inames ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                Pulse_Reflection_Util.inames_lid))
    | Pulse_Syntax.Tm_EmpInames -> Pulse_Reflection_Util.emp_inames_tm
    | Pulse_Syntax.Tm_UVar uu___ ->
        FStar_Reflection_Builtins.pack_ln FStar_Reflection_Data.Tv_Unknown
    | Pulse_Syntax.Tm_Unknown ->
        FStar_Reflection_Builtins.pack_ln FStar_Reflection_Data.Tv_Unknown
and (elab_comp : Pulse_Syntax.comp -> FStar_Reflection_Types.term) =
  fun c ->
    match c with
    | Pulse_Syntax.C_Tot t -> elab_term t
    | Pulse_Syntax.C_ST c1 ->
        let uu___ = elab_st_comp c1 in
        (match uu___ with
         | (u, res, pre, post) ->
             Pulse_Reflection_Util.mk_stt_comp u res pre
               (Pulse_Reflection_Util.mk_abs res
                  FStar_Reflection_Data.Q_Explicit post))
    | Pulse_Syntax.C_STAtomic (inames, c1) ->
        let inames1 = elab_term inames in
        let uu___ = elab_st_comp c1 in
        (match uu___ with
         | (u, res, pre, post) ->
             Pulse_Reflection_Util.mk_stt_atomic_comp u res inames1 pre
               (Pulse_Reflection_Util.mk_abs res
                  FStar_Reflection_Data.Q_Explicit post))
    | Pulse_Syntax.C_STGhost (inames, c1) ->
        let inames1 = elab_term inames in
        let uu___ = elab_st_comp c1 in
        (match uu___ with
         | (u, res, pre, post) ->
             Pulse_Reflection_Util.mk_stt_ghost_comp u res inames1 pre
               (Pulse_Reflection_Util.mk_abs res
                  FStar_Reflection_Data.Q_Explicit post))
and (elab_st_comp :
  Pulse_Syntax.st_comp ->
    (FStar_Reflection_Types.universe * FStar_Reflection_Types.term *
      FStar_Reflection_Types.term * FStar_Reflection_Types.term))
  =
  fun c ->
    let res = elab_term c.Pulse_Syntax.res in
    let pre = elab_term c.Pulse_Syntax.pre in
    let post = elab_term c.Pulse_Syntax.post in
    ((elab_universe c.Pulse_Syntax.u), res, pre, post)
let (elab_stt_equiv :
  FStar_Reflection_Types.env ->
    Pulse_Syntax.comp ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (unit, unit, unit) FStar_Reflection_Typing.equiv ->
            (unit, unit, unit) FStar_Reflection_Typing.equiv ->
              (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun c ->
      fun pre ->
        fun post ->
          fun eq_pre ->
            fun eq_post ->
              Pulse_Reflection_Util.mk_stt_comp_equiv g
                (elab_universe (Pulse_Syntax.comp_u c))
                (elab_term (Pulse_Syntax.comp_res c)) pre post
                (elab_term (Pulse_Syntax.comp_pre c))
                (Pulse_Reflection_Util.mk_abs
                   (elab_term (Pulse_Syntax.comp_res c))
                   FStar_Reflection_Data.Q_Explicit
                   (elab_term (Pulse_Syntax.comp_post c))) eq_pre eq_post
let (elab_statomic_equiv :
  FStar_Reflection_Types.env ->
    Pulse_Syntax.comp ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (unit, unit, unit) FStar_Reflection_Typing.equiv ->
            (unit, unit, unit) FStar_Reflection_Typing.equiv ->
              (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun c ->
      fun pre ->
        fun post ->
          fun eq_pre ->
            fun eq_post ->
              let uu___ = c in
              match uu___ with
              | Pulse_Syntax.C_STAtomic (inames, uu___1) ->
                  Pulse_Reflection_Util.mk_stt_atomic_comp_equiv g
                    (elab_universe (Pulse_Syntax.comp_u c))
                    (elab_term (Pulse_Syntax.comp_res c)) (elab_term inames)
                    pre post (elab_term (Pulse_Syntax.comp_pre c))
                    (Pulse_Reflection_Util.mk_abs
                       (elab_term (Pulse_Syntax.comp_res c))
                       FStar_Reflection_Data.Q_Explicit
                       (elab_term (Pulse_Syntax.comp_post c))) eq_pre eq_post
let (elab_stghost_equiv :
  FStar_Reflection_Types.env ->
    Pulse_Syntax.comp ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (unit, unit, unit) FStar_Reflection_Typing.equiv ->
            (unit, unit, unit) FStar_Reflection_Typing.equiv ->
              (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun c ->
      fun pre ->
        fun post ->
          fun eq_pre ->
            fun eq_post ->
              let uu___ = c in
              match uu___ with
              | Pulse_Syntax.C_STGhost (inames, uu___1) ->
                  Pulse_Reflection_Util.mk_stt_ghost_comp_equiv g
                    (elab_universe (Pulse_Syntax.comp_u c))
                    (elab_term (Pulse_Syntax.comp_res c)) (elab_term inames)
                    pre post (elab_term (Pulse_Syntax.comp_pre c))
                    (Pulse_Reflection_Util.mk_abs
                       (elab_term (Pulse_Syntax.comp_res c))
                       FStar_Reflection_Data.Q_Explicit
                       (elab_term (Pulse_Syntax.comp_post c))) eq_pre eq_post