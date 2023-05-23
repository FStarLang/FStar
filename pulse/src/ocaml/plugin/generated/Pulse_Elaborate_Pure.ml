open Prims
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
let (elab_qual :
  Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
    FStar_Reflection_Data.aqualv)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_Reflection_Data.Q_Explicit
    | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Implicit) ->
        FStar_Reflection_Data.Q_Implicit
let (embedded_uvar_lid : Prims.string Prims.list) =
  ["__pulse_embedded_uvar__"]
let (embed_uvar : Prims.nat -> FStar_Reflection_Types.term) =
  fun n ->
    FStar_Reflection_Builtins.pack_ln
      (FStar_Reflection_Data.Tv_UInst
         ((FStar_Reflection_Builtins.pack_fv embedded_uvar_lid),
           [FStar_Reflection_Builtins.pack_universe
              (FStar_Reflection_Data.Uv_BVar n)]))
let rec (elab_term : Pulse_Syntax_Base.term -> FStar_Reflection_Types.term) =
  fun top ->
    match top with
    | Pulse_Syntax_Base.Tm_VProp ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                Pulse_Reflection_Util.vprop_lid))
    | Pulse_Syntax_Base.Tm_Emp ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv Pulse_Reflection_Util.emp_lid))
    | Pulse_Syntax_Base.Tm_Pure p ->
        let p1 = elab_term p in
        let head =
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_FVar
               (FStar_Reflection_Builtins.pack_fv
                  Pulse_Reflection_Util.pure_lid)) in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             (head, (p1, FStar_Reflection_Data.Q_Explicit)))
    | Pulse_Syntax_Base.Tm_Star (l, r) ->
        let l1 = elab_term l in
        let r1 = elab_term r in Pulse_Reflection_Util.mk_star l1 r1
    | Pulse_Syntax_Base.Tm_ExistsSL (u, t, body, uu___) ->
        let t1 = elab_term t in
        let b = elab_term body in
        if Pulse_Syntax_Base.uu___is_Tm_ExistsSL top
        then
          Pulse_Reflection_Util.mk_exists u t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
        else
          Pulse_Reflection_Util.mk_forall u t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
    | Pulse_Syntax_Base.Tm_ForallSL (u, t, body) ->
        let t1 = elab_term t in
        let b = elab_term body in
        if Pulse_Syntax_Base.uu___is_Tm_ExistsSL top
        then
          Pulse_Reflection_Util.mk_exists u t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
        else
          Pulse_Reflection_Util.mk_forall u t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
    | Pulse_Syntax_Base.Tm_Inames ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                Pulse_Reflection_Util.inames_lid))
    | Pulse_Syntax_Base.Tm_EmpInames -> Pulse_Reflection_Util.emp_inames_tm
    | Pulse_Syntax_Base.Tm_UVar n -> embed_uvar n
    | Pulse_Syntax_Base.Tm_Unknown ->
        FStar_Reflection_Builtins.pack_ln FStar_Reflection_Data.Tv_Unknown
    | Pulse_Syntax_Base.Tm_FStar (t, uu___) -> t
let (elab_st_comp :
  Pulse_Syntax_Base.st_comp ->
    (FStar_Reflection_Types.universe * FStar_Reflection_Types.term *
      FStar_Reflection_Types.term * FStar_Reflection_Types.term))
  =
  fun c ->
    let res = elab_term c.Pulse_Syntax_Base.res in
    let pre = elab_term c.Pulse_Syntax_Base.pre in
    let post = elab_term c.Pulse_Syntax_Base.post in
    ((c.Pulse_Syntax_Base.u), res, pre, post)
let (elab_comp : Pulse_Syntax_Base.comp -> FStar_Reflection_Types.term) =
  fun c ->
    match c with
    | Pulse_Syntax_Base.C_Tot t -> elab_term t
    | Pulse_Syntax_Base.C_ST c1 ->
        let uu___ = elab_st_comp c1 in
        (match uu___ with
         | (u, res, pre, post) ->
             Pulse_Reflection_Util.mk_stt_comp u res pre
               (Pulse_Reflection_Util.mk_abs res
                  FStar_Reflection_Data.Q_Explicit post))
    | Pulse_Syntax_Base.C_STAtomic (inames, c1) ->
        let inames1 = elab_term inames in
        let uu___ = elab_st_comp c1 in
        (match uu___ with
         | (u, res, pre, post) ->
             Pulse_Reflection_Util.mk_stt_atomic_comp u res inames1 pre
               (Pulse_Reflection_Util.mk_abs res
                  FStar_Reflection_Data.Q_Explicit post))
    | Pulse_Syntax_Base.C_STGhost (inames, c1) ->
        let inames1 = elab_term inames in
        let uu___ = elab_st_comp c1 in
        (match uu___ with
         | (u, res, pre, post) ->
             Pulse_Reflection_Util.mk_stt_ghost_comp u res inames1 pre
               (Pulse_Reflection_Util.mk_abs res
                  FStar_Reflection_Data.Q_Explicit post))
let (elab_stt_equiv :
  FStar_Reflection_Types.env ->
    Pulse_Syntax_Base.comp ->
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
                (Pulse_Syntax_Base.comp_u c)
                (elab_term (Pulse_Syntax_Base.comp_res c)) pre post
                (elab_term (Pulse_Syntax_Base.comp_pre c))
                (Pulse_Reflection_Util.mk_abs
                   (elab_term (Pulse_Syntax_Base.comp_res c))
                   FStar_Reflection_Data.Q_Explicit
                   (elab_term (Pulse_Syntax_Base.comp_post c))) eq_pre
                eq_post
let (elab_statomic_equiv :
  FStar_Reflection_Types.env ->
    Pulse_Syntax_Base.comp ->
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
              | Pulse_Syntax_Base.C_STAtomic (inames, uu___1) ->
                  Pulse_Reflection_Util.mk_stt_atomic_comp_equiv g
                    (Pulse_Syntax_Base.comp_u c)
                    (elab_term (Pulse_Syntax_Base.comp_res c))
                    (elab_term inames) pre post
                    (elab_term (Pulse_Syntax_Base.comp_pre c))
                    (Pulse_Reflection_Util.mk_abs
                       (elab_term (Pulse_Syntax_Base.comp_res c))
                       FStar_Reflection_Data.Q_Explicit
                       (elab_term (Pulse_Syntax_Base.comp_post c))) eq_pre
                    eq_post
let (elab_stghost_equiv :
  FStar_Reflection_Types.env ->
    Pulse_Syntax_Base.comp ->
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
              | Pulse_Syntax_Base.C_STGhost (inames, uu___1) ->
                  Pulse_Reflection_Util.mk_stt_ghost_comp_equiv g
                    (Pulse_Syntax_Base.comp_u c)
                    (elab_term (Pulse_Syntax_Base.comp_res c))
                    (elab_term inames) pre post
                    (elab_term (Pulse_Syntax_Base.comp_pre c))
                    (Pulse_Reflection_Util.mk_abs
                       (elab_term (Pulse_Syntax_Base.comp_res c))
                       FStar_Reflection_Data.Q_Explicit
                       (elab_term (Pulse_Syntax_Base.comp_post c))) eq_pre
                    eq_post
let (u0 : Pulse_Syntax_Base.universe) =
  FStar_Reflection_Builtins.pack_universe FStar_Reflection_Data.Uv_Zero
let (u1 : Pulse_Syntax_Base.universe) =
  FStar_Reflection_Builtins.pack_universe (FStar_Reflection_Data.Uv_Succ u0)
let (u2 : Pulse_Syntax_Base.universe) =
  FStar_Reflection_Builtins.pack_universe (FStar_Reflection_Data.Uv_Succ u1)
let (u_zero : Pulse_Syntax_Base.universe) = u0
let (u_succ : Pulse_Syntax_Base.universe -> Pulse_Syntax_Base.universe) =
  fun u ->
    FStar_Reflection_Builtins.pack_universe (FStar_Reflection_Data.Uv_Succ u)
let (u_var : Prims.string -> Pulse_Syntax_Base.universe) =
  fun s ->
    FStar_Reflection_Builtins.pack_universe
      (FStar_Reflection_Data.Uv_Name (s, FStar_Range.range_0))
let (u_max :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.universe -> Pulse_Syntax_Base.universe)
  =
  fun u01 ->
    fun u11 ->
      FStar_Reflection_Builtins.pack_universe
        (FStar_Reflection_Data.Uv_Max [u01; u11])
let (u_unknown : Pulse_Syntax_Base.universe) =
  FStar_Reflection_Builtins.pack_universe FStar_Reflection_Data.Uv_Unk
let (tm_bvar : Pulse_Syntax_Base.bv -> Pulse_Syntax_Base.term) =
  fun bv ->
    Pulse_Syntax_Base.Tm_FStar
      ((FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_BVar
             (FStar_Reflection_Builtins.pack_bv
                (FStar_Reflection_Typing.make_bv_with_name
                   bv.Pulse_Syntax_Base.bv_ppname
                   bv.Pulse_Syntax_Base.bv_index)))),
        (bv.Pulse_Syntax_Base.bv_range))
let (tm_var : Pulse_Syntax_Base.nm -> Pulse_Syntax_Base.term) =
  fun nm ->
    Pulse_Syntax_Base.Tm_FStar
      ((FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_Var
             (FStar_Reflection_Builtins.pack_bv
                (FStar_Reflection_Typing.make_bv_with_name
                   nm.Pulse_Syntax_Base.nm_ppname
                   nm.Pulse_Syntax_Base.nm_index)))),
        (nm.Pulse_Syntax_Base.nm_range))
let (tm_fvar : Pulse_Syntax_Base.fv -> Pulse_Syntax_Base.term) =
  fun l ->
    Pulse_Syntax_Base.Tm_FStar
      ((FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv l.Pulse_Syntax_Base.fv_name))),
        (l.Pulse_Syntax_Base.fv_range))
let (tm_uinst :
  Pulse_Syntax_Base.fv ->
    Pulse_Syntax_Base.universe Prims.list -> Pulse_Syntax_Base.term)
  =
  fun l ->
    fun us ->
      Pulse_Syntax_Base.Tm_FStar
        ((FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_UInst
               ((FStar_Reflection_Builtins.pack_fv
                   l.Pulse_Syntax_Base.fv_name), us))),
          (l.Pulse_Syntax_Base.fv_range))
let (tm_constant : Pulse_Syntax_Base.constant -> Pulse_Syntax_Base.term) =
  fun c ->
    Pulse_Syntax_Base.Tm_FStar
      ((FStar_Reflection_Builtins.pack_ln (FStar_Reflection_Data.Tv_Const c)),
        FStar_Range.range_0)
let (tm_refine :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun b ->
    fun t ->
      Pulse_Syntax_Base.Tm_FStar
        ((FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Refine
               ((FStar_Reflection_Builtins.pack_bv
                   (FStar_Reflection_Typing.make_bv_with_name
                      b.Pulse_Syntax_Base.binder_ppname Prims.int_zero)),
                 (elab_term b.Pulse_Syntax_Base.binder_ty), (elab_term t)))),
          FStar_Range.range_0)
let (tm_let :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun t ->
    fun e1 ->
      fun e2 ->
        Pulse_Syntax_Base.Tm_FStar
          ((FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_Let
                 (false, [],
                   (FStar_Reflection_Builtins.pack_bv
                      (FStar_Reflection_Typing.make_bv Prims.int_zero)),
                   (elab_term t), (elab_term e1), (elab_term e2)))),
            FStar_Range.range_0)
let (tm_pureapp :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun head ->
    fun q ->
      fun arg ->
        Pulse_Syntax_Base.Tm_FStar
          ((FStar_Reflection_Derived.mk_app (elab_term head)
              [((elab_term arg), (elab_qual q))]), FStar_Range.range_0)
let (tm_arrow :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.term)
  =
  fun b ->
    fun q ->
      fun c ->
        Pulse_Syntax_Base.Tm_FStar
          ((Pulse_Reflection_Util.mk_arrow_with_name
              b.Pulse_Syntax_Base.binder_ppname
              ((elab_term b.Pulse_Syntax_Base.binder_ty), (elab_qual q))
              (elab_comp c)), FStar_Range.range_0)
let (tm_type : Pulse_Syntax_Base.universe -> Pulse_Syntax_Base.term) =
  fun u ->
    Pulse_Syntax_Base.Tm_FStar
      ((FStar_Reflection_Builtins.pack_ln (FStar_Reflection_Data.Tv_Type u)),
        FStar_Range.range_0)
let (mk_bvar :
  Prims.string ->
    FStar_Range.range -> Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term)
  =
  fun s ->
    fun r ->
      fun i ->
        tm_bvar
          {
            Pulse_Syntax_Base.bv_index = i;
            Pulse_Syntax_Base.bv_ppname =
              (FStar_Reflection_Typing.seal_pp_name s);
            Pulse_Syntax_Base.bv_range = r
          }
let (null_var : Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term) =
  fun v ->
    tm_var
      {
        Pulse_Syntax_Base.nm_index = v;
        Pulse_Syntax_Base.nm_ppname = FStar_Reflection_Typing.pp_name_default;
        Pulse_Syntax_Base.nm_range = FStar_Range.range_0
      }
let (null_bvar : Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term) =
  fun i ->
    tm_bvar
      {
        Pulse_Syntax_Base.bv_index = i;
        Pulse_Syntax_Base.bv_ppname = FStar_Reflection_Typing.pp_name_default;
        Pulse_Syntax_Base.bv_range = FStar_Range.range_0
      }
let (term_of_nvar : Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.term) =
  fun x ->
    tm_var
      {
        Pulse_Syntax_Base.nm_index = (FStar_Pervasives_Native.snd x);
        Pulse_Syntax_Base.nm_ppname = (FStar_Pervasives_Native.fst x);
        Pulse_Syntax_Base.nm_range = FStar_Range.range_0
      }
let (term_of_no_name_var : Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term) =
  fun x -> term_of_nvar (Pulse_Syntax_Base.v_as_nv x)