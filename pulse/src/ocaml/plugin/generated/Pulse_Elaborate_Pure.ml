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
    FStar_Reflection_V2_Data.aqualv)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_Reflection_V2_Data.Q_Explicit
    | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Implicit) ->
        FStar_Reflection_V2_Data.Q_Implicit
let (elab_observability :
  Pulse_Syntax_Base.observability -> FStar_Reflection_Types.term) =
  fun uu___ ->
    match uu___ with
    | Pulse_Syntax_Base.Neutral ->
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                Pulse_Reflection_Util.neutral_lid))
    | Pulse_Syntax_Base.Observable ->
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                Pulse_Reflection_Util.observable_lid))
let (elab_term : Pulse_Syntax_Base.term -> FStar_Reflection_Types.term) =
  fun top -> top
let rec (elab_pat :
  Pulse_Syntax_Base.pattern -> FStar_Reflection_V2_Data.pattern) =
  fun p ->
    let elab_fv f =
      FStar_Reflection_V2_Builtins.pack_fv f.Pulse_Syntax_Base.fv_name in
    match p with
    | Pulse_Syntax_Base.Pat_Constant c ->
        FStar_Reflection_V2_Data.Pat_Constant c
    | Pulse_Syntax_Base.Pat_Var (v, ty) ->
        FStar_Reflection_V2_Data.Pat_Var
          (FStar_Reflection_Typing.sort_default, v)
    | Pulse_Syntax_Base.Pat_Cons (fv, vs) ->
        FStar_Reflection_V2_Data.Pat_Cons
          ((elab_fv fv), FStar_Pervasives_Native.None,
            (Pulse_Common.map_dec p vs elab_sub_pat))
    | Pulse_Syntax_Base.Pat_Dot_Term (FStar_Pervasives_Native.None) ->
        FStar_Reflection_V2_Data.Pat_Dot_Term FStar_Pervasives_Native.None
    | Pulse_Syntax_Base.Pat_Dot_Term (FStar_Pervasives_Native.Some t) ->
        FStar_Reflection_V2_Data.Pat_Dot_Term
          (FStar_Pervasives_Native.Some (elab_term t))
and (elab_sub_pat :
  (Pulse_Syntax_Base.pattern * Prims.bool) ->
    (FStar_Reflection_V2_Data.pattern * Prims.bool))
  =
  fun pi -> let uu___ = pi in match uu___ with | (p, i) -> ((elab_pat p), i)
let (elab_pats :
  Pulse_Syntax_Base.pattern Prims.list ->
    FStar_Reflection_V2_Data.pattern Prims.list)
  = fun ps -> FStar_List_Tot_Base.map elab_pat ps
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
                  FStar_Reflection_V2_Data.Q_Explicit post))
    | Pulse_Syntax_Base.C_STAtomic (inames, obs, c1) ->
        let inames1 = elab_term inames in
        let uu___ = elab_st_comp c1 in
        (match uu___ with
         | (u, res, pre, post) ->
             let post1 =
               Pulse_Reflection_Util.mk_abs res
                 FStar_Reflection_V2_Data.Q_Explicit post in
             Pulse_Reflection_Util.mk_stt_atomic_comp
               (elab_observability obs) u res inames1 pre post1)
    | Pulse_Syntax_Base.C_STGhost (inames, c1) ->
        let inames1 = elab_term inames in
        let uu___ = elab_st_comp c1 in
        (match uu___ with
         | (u, res, pre, post) ->
             Pulse_Reflection_Util.mk_stt_ghost_comp u res inames1 pre
               (Pulse_Reflection_Util.mk_abs res
                  FStar_Reflection_V2_Data.Q_Explicit post))
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
                (elab_term (Pulse_Syntax_Base.comp_res c))
                (elab_term (Pulse_Syntax_Base.comp_pre c))
                (Pulse_Reflection_Util.mk_abs
                   (elab_term (Pulse_Syntax_Base.comp_res c))
                   FStar_Reflection_V2_Data.Q_Explicit
                   (elab_term (Pulse_Syntax_Base.comp_post c)))
                (FStar_Reflection_Typing.Rel_refl
                   (g, (elab_term (Pulse_Syntax_Base.comp_res c)),
                     FStar_Reflection_Typing.R_Eq)) eq_pre eq_post
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
              | Pulse_Syntax_Base.C_STAtomic
                  (inames, obs,
                   { Pulse_Syntax_Base.u = u; Pulse_Syntax_Base.res = res;
                     Pulse_Syntax_Base.pre = uu___1;
                     Pulse_Syntax_Base.post = uu___2;_})
                  ->
                  let c' =
                    Pulse_Reflection_Util.mk_stt_atomic_comp
                      (elab_observability obs) u (elab_term res)
                      (elab_term inames) pre post in
                  Pulse_Reflection_Util.mk_stt_atomic_comp_equiv g
                    (elab_observability obs) (Pulse_Syntax_Base.comp_u c)
                    (elab_term (Pulse_Syntax_Base.comp_res c))
                    (elab_term inames) pre post
                    (elab_term (Pulse_Syntax_Base.comp_pre c))
                    (Pulse_Reflection_Util.mk_abs
                       (elab_term (Pulse_Syntax_Base.comp_res c))
                       FStar_Reflection_V2_Data.Q_Explicit
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
                       FStar_Reflection_V2_Data.Q_Explicit
                       (elab_term (Pulse_Syntax_Base.comp_post c))) eq_pre
                    eq_post