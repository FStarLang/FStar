open Prims
let op_let_Question :
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
let (u0 : Pulse_Syntax_Base.universe) =
  FStar_Reflection_V2_Builtins.pack_universe FStar_Reflection_V2_Data.Uv_Zero
let (u1 : Pulse_Syntax_Base.universe) =
  FStar_Reflection_V2_Builtins.pack_universe
    (FStar_Reflection_V2_Data.Uv_Succ u0)
let (u2 : Pulse_Syntax_Base.universe) =
  FStar_Reflection_V2_Builtins.pack_universe
    (FStar_Reflection_V2_Data.Uv_Succ u1)
let (u_zero : Pulse_Syntax_Base.universe) = u0
let (u_one : Pulse_Syntax_Base.universe) = u1
let (u_succ : Pulse_Syntax_Base.universe -> Pulse_Syntax_Base.universe) =
  fun u ->
    FStar_Reflection_V2_Builtins.pack_universe
      (FStar_Reflection_V2_Data.Uv_Succ u)
let (u_var : Prims.string -> Pulse_Syntax_Base.universe) =
  fun s ->
    FStar_Reflection_V2_Builtins.pack_universe
      (FStar_Reflection_V2_Data.Uv_Name
         (FStar_Reflection_V2_Builtins.pack_ident (s, FStar_Range.range_0)))
let (u_max :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.universe -> Pulse_Syntax_Base.universe)
  =
  fun u01 ->
    fun u11 ->
      FStar_Reflection_V2_Builtins.pack_universe
        (FStar_Reflection_V2_Data.Uv_Max [u01; u11])
let (u_unknown : Pulse_Syntax_Base.universe) =
  FStar_Reflection_V2_Builtins.pack_universe FStar_Reflection_V2_Data.Uv_Unk
let (tm_bvar : Pulse_Syntax_Base.bv -> Pulse_Syntax_Base.term) =
  fun bv ->
    Pulse_RuntimeUtils.set_range
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_BVar
            (FStar_Reflection_V2_Builtins.pack_bv
               (FStar_Reflection_Typing.make_bv_with_name
                  (bv.Pulse_Syntax_Base.bv_ppname).Pulse_Syntax_Base.name
                  bv.Pulse_Syntax_Base.bv_index))))
      (bv.Pulse_Syntax_Base.bv_ppname).Pulse_Syntax_Base.range
let (tm_var : Pulse_Syntax_Base.nm -> Pulse_Syntax_Base.term) =
  fun nm ->
    Pulse_RuntimeUtils.set_range
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_Var
            (FStar_Reflection_V2_Builtins.pack_namedv
               (FStar_Reflection_Typing.make_namedv_with_name
                  (nm.Pulse_Syntax_Base.nm_ppname).Pulse_Syntax_Base.name
                  nm.Pulse_Syntax_Base.nm_index))))
      (nm.Pulse_Syntax_Base.nm_ppname).Pulse_Syntax_Base.range
let (tm_fvar : Pulse_Syntax_Base.fv -> Pulse_Syntax_Base.term) =
  fun l ->
    Pulse_RuntimeUtils.set_range
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv l.Pulse_Syntax_Base.fv_name)))
      l.Pulse_Syntax_Base.fv_range
let (tm_uinst :
  Pulse_Syntax_Base.fv ->
    Pulse_Syntax_Base.universe Prims.list -> Pulse_Syntax_Base.term)
  =
  fun l ->
    fun us ->
      Pulse_RuntimeUtils.set_range
        (FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_UInst
              ((FStar_Reflection_V2_Builtins.pack_fv
                  l.Pulse_Syntax_Base.fv_name), us)))
        l.Pulse_Syntax_Base.fv_range
let (tm_constant : Pulse_Syntax_Base.constant -> Pulse_Syntax_Base.term) =
  fun c ->
    Pulse_RuntimeUtils.set_range
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_Const c)) FStar_Range.range_0
let (tm_refine :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun b ->
    fun t ->
      let rb =
        FStar_Reflection_Typing.mk_simple_binder
          (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name
          b.Pulse_Syntax_Base.binder_ty in
      Pulse_RuntimeUtils.set_range
        (FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_Refine (rb, t))) FStar_Range.range_0
let (tm_let :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun t ->
    fun e1 ->
      fun e2 ->
        let rb =
          FStar_Reflection_Typing.mk_simple_binder
            FStar_Reflection_Typing.pp_name_default t in
        Pulse_RuntimeUtils.set_range
          (FStar_Reflection_V2_Builtins.pack_ln
             (FStar_Reflection_V2_Data.Tv_Let (false, [], rb, e1, e2)))
          FStar_Range.range_0
let (tm_pureapp :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun head ->
    fun q ->
      fun arg ->
        Pulse_RuntimeUtils.set_range
          (FStar_Reflection_V2_Derived.mk_app head
             [(arg, (Pulse_Elaborate_Pure.elab_qual q))]) FStar_Range.range_0
let (tm_pureabs :
  FStar_Reflection_V2_Data.ppname_t ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun ppname ->
    fun ty ->
      fun q ->
        fun body ->
          let b =
            {
              FStar_Tactics_NamedView.uniq = Prims.int_zero;
              FStar_Tactics_NamedView.ppname = ppname;
              FStar_Tactics_NamedView.sort = ty;
              FStar_Tactics_NamedView.qual =
                (Pulse_Elaborate_Pure.elab_qual q);
              FStar_Tactics_NamedView.attrs = []
            } in
          let r =
            FStar_Tactics_NamedView.pack
              (FStar_Tactics_NamedView.Tv_Abs (b, body)) in
          Pulse_RuntimeUtils.set_range r FStar_Range.range_0
let (tm_arrow :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.term)
  =
  fun b ->
    fun q ->
      fun c ->
        Pulse_RuntimeUtils.set_range
          (Pulse_Reflection_Util.mk_arrow_with_name
             (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name
             ((b.Pulse_Syntax_Base.binder_ty),
               (Pulse_Elaborate_Pure.elab_qual q))
             (Pulse_Elaborate_Pure.elab_comp c)) FStar_Range.range_0
let (tm_type : Pulse_Syntax_Base.universe -> Pulse_Syntax_Base.term) =
  fun u -> FStar_Reflection_Typing.tm_type u
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
              (Pulse_Syntax_Base.mk_ppname
                 (FStar_Reflection_Typing.seal_pp_name s) r)
          }
let (null_var : Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term) =
  fun v ->
    tm_var
      {
        Pulse_Syntax_Base.nm_index = v;
        Pulse_Syntax_Base.nm_ppname = Pulse_Syntax_Base.ppname_default
      }
let (null_bvar : Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term) =
  fun i ->
    tm_bvar
      {
        Pulse_Syntax_Base.bv_index = i;
        Pulse_Syntax_Base.bv_ppname = Pulse_Syntax_Base.ppname_default
      }
let (term_of_nvar : Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.term) =
  fun x ->
    tm_var
      {
        Pulse_Syntax_Base.nm_index = (FStar_Pervasives_Native.snd x);
        Pulse_Syntax_Base.nm_ppname = (FStar_Pervasives_Native.fst x)
      }
let (term_of_no_name_var : Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term) =
  fun x -> term_of_nvar (Pulse_Syntax_Base.v_as_nv x)
let (is_bvar :
  Pulse_Syntax_Base.term -> Prims.nat FStar_Pervasives_Native.option) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_BVar bv ->
        let bv_view = FStar_Reflection_V2_Builtins.inspect_bv bv in
        FStar_Pervasives_Native.Some (bv_view.FStar_Reflection_V2_Data.index)
    | uu___ -> FStar_Pervasives_Native.None
let (is_var :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.nm FStar_Pervasives_Native.option)
  =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_Var nv ->
        let nv_view = FStar_Reflection_V2_Builtins.inspect_namedv nv in
        FStar_Pervasives_Native.Some
          {
            Pulse_Syntax_Base.nm_index =
              (nv_view.FStar_Reflection_V2_Data.uniq);
            Pulse_Syntax_Base.nm_ppname =
              (Pulse_Syntax_Base.mk_ppname
                 nv_view.FStar_Reflection_V2_Data.ppname
                 (FStar_Reflection_V2_Builtins.range_of_term t))
          }
    | uu___ -> FStar_Pervasives_Native.None
let (is_fvar :
  Pulse_Syntax_Base.term ->
    (FStar_Reflection_Types.name * Pulse_Syntax_Base.universe Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_FVar fv ->
        FStar_Pervasives_Native.Some
          ((FStar_Reflection_V2_Builtins.inspect_fv fv), [])
    | FStar_Reflection_V2_Data.Tv_UInst (fv, us) ->
        FStar_Pervasives_Native.Some
          ((FStar_Reflection_V2_Builtins.inspect_fv fv), us)
    | uu___ -> FStar_Pervasives_Native.None
let (readback_qual :
  FStar_Reflection_V2_Data.aqualv ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Reflection_V2_Data.Q_Implicit ->
        FStar_Pervasives_Native.Some Pulse_Syntax_Base.Implicit
    | uu___1 -> FStar_Pervasives_Native.None
let (is_pure_app :
  Pulse_Syntax_Base.term ->
    (Pulse_Syntax_Base.term * Pulse_Syntax_Base.qualifier
      FStar_Pervasives_Native.option * Pulse_Syntax_Base.term)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_App (hd, (arg, q)) ->
        let q1 = readback_qual q in
        FStar_Pervasives_Native.Some (hd, q1, arg)
    | uu___ -> FStar_Pervasives_Native.None
let (leftmost_head :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = FStar_Reflection_V2_Derived.collect_app_ln t in
    match uu___ with | (hd, uu___1) -> FStar_Pervasives_Native.Some hd
let (is_fvar_app :
  Pulse_Syntax_Base.term ->
    (FStar_Reflection_Types.name * Pulse_Syntax_Base.universe Prims.list *
      Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option *
      Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match is_fvar t with
    | FStar_Pervasives_Native.Some (l, us) ->
        FStar_Pervasives_Native.Some
          (l, us, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
    | FStar_Pervasives_Native.None ->
        (match is_pure_app t with
         | FStar_Pervasives_Native.Some (head, q, arg) ->
             (match is_fvar head with
              | FStar_Pervasives_Native.Some (l, us) ->
                  FStar_Pervasives_Native.Some
                    (l, us, q, (FStar_Pervasives_Native.Some arg))
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
         | uu___ -> FStar_Pervasives_Native.None)
let (is_arrow :
  Pulse_Syntax_Base.term ->
    (Pulse_Syntax_Base.binder * Pulse_Syntax_Base.qualifier
      FStar_Pervasives_Native.option * Pulse_Syntax_Base.comp)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match FStar_Reflection_V2_Derived.inspect_ln_unascribe t with
    | FStar_Reflection_V2_Data.Tv_Arrow (b, c) ->
        let uu___ = FStar_Reflection_V2_Builtins.inspect_binder b in
        (match uu___ with
         | { FStar_Reflection_V2_Data.sort2 = sort;
             FStar_Reflection_V2_Data.qual = qual;
             FStar_Reflection_V2_Data.attrs = uu___1;
             FStar_Reflection_V2_Data.ppname2 = ppname;_} ->
             (match qual with
              | FStar_Reflection_V2_Data.Q_Meta uu___2 ->
                  FStar_Pervasives_Native.None
              | uu___2 ->
                  let q = readback_qual qual in
                  let c_view = FStar_Reflection_V2_Builtins.inspect_comp c in
                  let ret c_t =
                    let binder_ty = sort in
                    op_let_Question
                      (match Pulse_Readback.readback_comp c_t with
                       | FStar_Pervasives_Native.Some c1 ->
                           FStar_Pervasives_Native.Some c1
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None)
                      (fun c1 ->
                         FStar_Pervasives_Native.Some
                           ((Pulse_Syntax_Base.mk_binder_ppname binder_ty
                               (Pulse_Syntax_Base.mk_ppname ppname
                                  (FStar_Reflection_V2_Builtins.range_of_term
                                     t))), q, c1)) in
                  (match c_view with
                   | FStar_Reflection_V2_Data.C_Total c_t -> ret c_t
                   | FStar_Reflection_V2_Data.C_Eff
                       (uu___3, eff_name, c_t, uu___4, uu___5) ->
                       if eff_name = Pulse_Reflection_Util.tot_lid
                       then ret c_t
                       else FStar_Pervasives_Native.None
                   | uu___3 -> FStar_Pervasives_Native.None)))
    | uu___ -> FStar_Pervasives_Native.None
let (is_eq2 :
  Pulse_Syntax_Base.term ->
    (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term *
      Pulse_Syntax_Base.term) FStar_Pervasives_Native.option)
  =
  fun t ->
    match is_pure_app t with
    | FStar_Pervasives_Native.Some (head, FStar_Pervasives_Native.None, a2)
        ->
        (match is_pure_app head with
         | FStar_Pervasives_Native.Some
             (head1, FStar_Pervasives_Native.None, a1) ->
             (match is_pure_app head1 with
              | FStar_Pervasives_Native.Some
                  (head2, FStar_Pervasives_Native.Some
                   (Pulse_Syntax_Base.Implicit), ty)
                  ->
                  (match is_fvar head2 with
                   | FStar_Pervasives_Native.Some (l, uu___) ->
                       if
                         (l = ["Pulse"; "Steel"; "Wrapper"; "eq2_prop"]) ||
                           (l = ["Prims"; "eq2"])
                       then FStar_Pervasives_Native.Some (ty, a1, a2)
                       else FStar_Pervasives_Native.None
                   | uu___ -> FStar_Pervasives_Native.None)
              | uu___ -> FStar_Pervasives_Native.None)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (unreveal :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match is_pure_app t with
    | FStar_Pervasives_Native.Some (head, FStar_Pervasives_Native.None, arg)
        ->
        (match is_pure_app head with
         | FStar_Pervasives_Native.Some
             (head1, FStar_Pervasives_Native.Some
              (Pulse_Syntax_Base.Implicit), uu___)
             ->
             (match is_fvar head1 with
              | FStar_Pervasives_Native.Some (l, uu___1) ->
                  if l = ["FStar"; "Ghost"; "reveal"]
                  then FStar_Pervasives_Native.Some arg
                  else FStar_Pervasives_Native.None
              | uu___1 -> FStar_Pervasives_Native.None)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (mk_squash :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun u ->
    fun t ->
      tm_pureapp
        (tm_uinst (Pulse_Syntax_Base.as_fv FStar_Reflection_Const.squash_qn)
           [u]) FStar_Pervasives_Native.None t
type term_view =
  | Tm_Emp 
  | Tm_Pure of Pulse_Syntax_Base.term 
  | Tm_Star of Pulse_Syntax_Base.vprop * Pulse_Syntax_Base.vprop 
  | Tm_ExistsSL of Pulse_Syntax_Base.universe * Pulse_Syntax_Base.binder *
  Pulse_Syntax_Base.vprop 
  | Tm_ForallSL of Pulse_Syntax_Base.universe * Pulse_Syntax_Base.binder *
  Pulse_Syntax_Base.vprop 
  | Tm_VProp 
  | Tm_Inv of Pulse_Syntax_Base.term * Pulse_Syntax_Base.vprop 
  | Tm_Inames 
  | Tm_EmpInames 
  | Tm_Unknown 
  | Tm_FStar of Pulse_Syntax_Base.term 
let uu___is_Tm_Emp uu___ = match uu___ with | Tm_Emp _ -> true | _ -> false
let uu___is_Tm_Pure uu___ = match uu___ with | Tm_Pure _ -> true | _ -> false
let uu___is_Tm_Star uu___ = match uu___ with | Tm_Star _ -> true | _ -> false
let uu___is_Tm_ExistsSL uu___ =
  match uu___ with | Tm_ExistsSL _ -> true | _ -> false
let uu___is_Tm_ForallSL uu___ =
  match uu___ with | Tm_ForallSL _ -> true | _ -> false
let uu___is_Tm_VProp uu___ =
  match uu___ with | Tm_VProp _ -> true | _ -> false
let uu___is_Tm_Inv uu___ = match uu___ with | Tm_Inv _ -> true | _ -> false
let uu___is_Tm_Inames uu___ =
  match uu___ with | Tm_Inames _ -> true | _ -> false
let uu___is_Tm_EmpInames uu___ =
  match uu___ with | Tm_EmpInames _ -> true | _ -> false
let uu___is_Tm_Unknown uu___ =
  match uu___ with | Tm_Unknown _ -> true | _ -> false
let uu___is_Tm_FStar uu___ =
  match uu___ with | Tm_FStar _ -> true | _ -> false
let (wr :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.range -> Pulse_Syntax_Base.term)
  = fun t -> fun r -> Pulse_RuntimeUtils.set_range t r
let (pack_term_view :
  term_view -> Pulse_Syntax_Base.range -> Pulse_Syntax_Base.term) =
  fun top ->
    fun r ->
      let w t' = wr t' r in
      match top with
      | Tm_VProp ->
          w
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     Pulse_Reflection_Util.vprop_lid)))
      | Tm_Emp ->
          w
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     Pulse_Reflection_Util.emp_lid)))
      | Tm_Inv (i, p) ->
          let head =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_FVar
                 (FStar_Reflection_V2_Builtins.pack_fv
                    Pulse_Reflection_Util.inv_lid)) in
          let t =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 (head, (i, FStar_Reflection_V2_Data.Q_Explicit))) in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               (t, (p, FStar_Reflection_V2_Data.Q_Explicit)))
      | Tm_Pure p ->
          let head =
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_FVar
                 (FStar_Reflection_V2_Builtins.pack_fv
                    Pulse_Reflection_Util.pure_lid)) in
          w
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_App
                  (head, (p, FStar_Reflection_V2_Data.Q_Explicit))))
      | Tm_Star (l, r1) -> w (Pulse_Reflection_Util.mk_star l r1)
      | Tm_ExistsSL (u, b, body) ->
          let t = b.Pulse_Syntax_Base.binder_ty in
          let abs =
            Pulse_Reflection_Util.mk_abs_with_name_and_range
              (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name
              (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.range t
              FStar_Reflection_V2_Data.Q_Explicit body in
          if uu___is_Tm_ExistsSL top
          then w (Pulse_Reflection_Util.mk_exists u t abs)
          else w (Pulse_Reflection_Util.mk_forall u t abs)
      | Tm_ForallSL (u, b, body) ->
          let t = b.Pulse_Syntax_Base.binder_ty in
          let abs =
            Pulse_Reflection_Util.mk_abs_with_name_and_range
              (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name
              (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.range t
              FStar_Reflection_V2_Data.Q_Explicit body in
          if uu___is_Tm_ExistsSL top
          then w (Pulse_Reflection_Util.mk_exists u t abs)
          else w (Pulse_Reflection_Util.mk_forall u t abs)
      | Tm_Inames ->
          w
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     Pulse_Reflection_Util.inames_lid)))
      | Tm_EmpInames ->
          w
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     Pulse_Reflection_Util.emp_inames_lid)))
      | Tm_Unknown ->
          w
            (FStar_Reflection_V2_Builtins.pack_ln
               FStar_Reflection_V2_Data.Tv_Unknown)
      | Tm_FStar t -> w t
let (term_range : Pulse_Syntax_Base.term -> FStar_Range.range) =
  fun t -> Pulse_RuntimeUtils.range_of_term t
let (pack_term_view_wr :
  term_view -> Pulse_Syntax_Base.range -> Pulse_Syntax_Base.term) =
  fun t -> fun r -> pack_term_view t r
let (tm_vprop : Pulse_Syntax_Base.term) =
  pack_term_view_wr Tm_VProp FStar_Range.range_0
let (tm_inames : Pulse_Syntax_Base.term) =
  pack_term_view_wr Tm_Inames FStar_Range.range_0
let (tm_emp : Pulse_Syntax_Base.term) =
  pack_term_view_wr Tm_Emp FStar_Range.range_0
let (tm_emp_inames : Pulse_Syntax_Base.term) =
  pack_term_view_wr Tm_EmpInames FStar_Range.range_0
let (tm_unknown : Pulse_Syntax_Base.term) =
  pack_term_view_wr Tm_Unknown FStar_Range.range_0
let (tm_pure : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term) =
  fun p -> pack_term_view (Tm_Pure p) (Pulse_RuntimeUtils.range_of_term p)
let (tm_star :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.term)
  =
  fun l ->
    fun r ->
      pack_term_view (Tm_Star (l, r))
        (Pulse_RuntimeUtils.union_ranges (Pulse_RuntimeUtils.range_of_term l)
           (Pulse_RuntimeUtils.range_of_term r))
let (tm_exists_sl :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.binder ->
      Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.term)
  =
  fun u ->
    fun b ->
      fun body ->
        pack_term_view (Tm_ExistsSL (u, b, body))
          (Pulse_RuntimeUtils.union_ranges
             (Pulse_RuntimeUtils.range_of_term b.Pulse_Syntax_Base.binder_ty)
             (Pulse_RuntimeUtils.range_of_term body))
let (tm_forall_sl :
  Pulse_Syntax_Base.universe ->
    Pulse_Syntax_Base.binder ->
      Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.term)
  =
  fun u ->
    fun b ->
      fun body ->
        pack_term_view (Tm_ForallSL (u, b, body))
          (Pulse_RuntimeUtils.union_ranges
             (Pulse_RuntimeUtils.range_of_term b.Pulse_Syntax_Base.binder_ty)
             (Pulse_RuntimeUtils.range_of_term body))
let (tm_iname_ref : Pulse_Syntax_Base.term) =
  tm_fvar (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.iname_ref_lid)
let (tm_inv :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun i ->
    fun p ->
      pack_term_view (Tm_Inv (i, p))
        (Pulse_RuntimeUtils.union_ranges (Pulse_RuntimeUtils.range_of_term i)
           (Pulse_RuntimeUtils.range_of_term p))
let (tm_all_inames : Pulse_Syntax_Base.term) =
  tm_fvar (Pulse_Syntax_Base.as_fv Pulse_Reflection_Util.all_inames_lid)
let (tm_add_inv :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun is ->
    fun iref ->
      let h =
        FStar_Reflection_V2_Builtins.pack_ln
          (FStar_Reflection_V2_Data.Tv_FVar
             (FStar_Reflection_V2_Builtins.pack_fv
                Pulse_Reflection_Util.add_inv_lid)) in
      FStar_Reflection_V2_Derived.mk_app h
        [Pulse_Reflection_Util.ex is; Pulse_Reflection_Util.ex iref]
let (tm_full_perm : Pulse_Syntax_Base.term) =
  tm_constant (FStar_Reflection_V2_Data.C_Real "1.0")
type ('tv, 't) is_view_of = Obj.t
let rec (inspect_term : FStar_Reflection_Types.term -> term_view) =
  fun t ->
    let default_view = Tm_FStar t in
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_FVar fv ->
        let fv_lid = FStar_Reflection_V2_Builtins.inspect_fv fv in
        if fv_lid = Pulse_Reflection_Util.vprop_lid
        then Tm_VProp
        else
          if fv_lid = Pulse_Reflection_Util.emp_lid
          then Tm_Emp
          else
            if fv_lid = Pulse_Reflection_Util.inames_lid
            then Tm_Inames
            else
              if fv_lid = Pulse_Reflection_Util.emp_inames_lid
              then Tm_EmpInames
              else default_view
    | FStar_Reflection_V2_Data.Tv_App (hd, (a, q)) ->
        let uu___ = FStar_Reflection_V2_Derived.collect_app_ln t in
        (match uu___ with
         | (head, args) ->
             (match ((FStar_Reflection_V2_Builtins.inspect_ln head), args)
              with
              | (FStar_Reflection_V2_Data.Tv_FVar fv, a1::a2::[]) ->
                  if
                    (FStar_Reflection_V2_Builtins.inspect_fv fv) =
                      Pulse_Reflection_Util.star_lid
                  then
                    Tm_Star
                      ((FStar_Pervasives_Native.fst a1),
                        (FStar_Pervasives_Native.fst a2))
                  else
                    if
                      (FStar_Reflection_V2_Builtins.inspect_fv fv) =
                        Pulse_Reflection_Util.inv_lid
                    then
                      Tm_Inv
                        ((FStar_Pervasives_Native.fst a1),
                          (FStar_Pervasives_Native.fst a2))
                    else default_view
              | (FStar_Reflection_V2_Data.Tv_UInst (fv, u::[]), a1::a2::[])
                  ->
                  if
                    ((FStar_Reflection_V2_Builtins.inspect_fv fv) =
                       Pulse_Reflection_Util.exists_lid)
                      ||
                      ((FStar_Reflection_V2_Builtins.inspect_fv fv) =
                         Pulse_Reflection_Util.forall_lid)
                  then
                    let t1 = FStar_Pervasives_Native.fst a1 in
                    let t2 = FStar_Pervasives_Native.fst a2 in
                    (match FStar_Reflection_V2_Builtins.inspect_ln t2 with
                     | FStar_Reflection_V2_Data.Tv_Abs (b, body) ->
                         let bview =
                           FStar_Reflection_V2_Builtins.inspect_binder b in
                         let b1 =
                           Pulse_Syntax_Base.mk_binder_ppname t1
                             (Pulse_Syntax_Base.mk_ppname
                                bview.FStar_Reflection_V2_Data.ppname2
                                (Pulse_RuntimeUtils.binder_range b)) in
                         if
                           (FStar_Reflection_V2_Builtins.inspect_fv fv) =
                             Pulse_Reflection_Util.exists_lid
                         then Tm_ExistsSL (u, b1, body)
                         else Tm_ForallSL (u, b1, body)
                     | uu___1 -> default_view)
                  else default_view
              | (FStar_Reflection_V2_Data.Tv_FVar fv, a1::[]) ->
                  if
                    (FStar_Reflection_V2_Builtins.inspect_fv fv) =
                      Pulse_Reflection_Util.pure_lid
                  then Tm_Pure (FStar_Pervasives_Native.fst a1)
                  else default_view
              | uu___1 -> default_view))
    | FStar_Reflection_V2_Data.Tv_Refine (uu___, uu___1) -> default_view
    | FStar_Reflection_V2_Data.Tv_Arrow (uu___, uu___1) -> default_view
    | FStar_Reflection_V2_Data.Tv_Type uu___ -> default_view
    | FStar_Reflection_V2_Data.Tv_Const uu___ -> default_view
    | FStar_Reflection_V2_Data.Tv_Let (uu___, uu___1, uu___2, uu___3, uu___4)
        -> default_view
    | FStar_Reflection_V2_Data.Tv_Var uu___ -> default_view
    | FStar_Reflection_V2_Data.Tv_BVar uu___ -> default_view
    | FStar_Reflection_V2_Data.Tv_UInst (uu___, uu___1) -> default_view
    | FStar_Reflection_V2_Data.Tv_Match (uu___, uu___1, uu___2) ->
        default_view
    | FStar_Reflection_V2_Data.Tv_Abs (uu___, uu___1) -> default_view
    | FStar_Reflection_V2_Data.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
        inspect_term t1
    | FStar_Reflection_V2_Data.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
        inspect_term t1
    | FStar_Reflection_V2_Data.Tv_Uvar (uu___, uu___1) -> default_view
    | FStar_Reflection_V2_Data.Tv_Unknown -> Tm_Unknown
    | FStar_Reflection_V2_Data.Tv_Unsupp -> default_view
let rec (vprop_as_list :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term Prims.list) =
  fun vp ->
    match inspect_term vp with
    | Tm_Emp -> []
    | Tm_Star (vp0, vp1) ->
        FStar_List_Tot_Base.append (vprop_as_list vp0) (vprop_as_list vp1)
    | uu___ -> [vp]
let rec (list_as_vprop :
  Pulse_Syntax_Base.term Prims.list -> Pulse_Syntax_Base.term) =
  fun vps ->
    match vps with
    | [] -> tm_emp
    | hd::[] -> hd
    | hd::tl -> tm_star hd (list_as_vprop tl)
let rec (insert1 :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term Prims.list ->
      (Pulse_Syntax_Base.term Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun ts ->
           match ts with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [t])))
           | t'::ts' ->
               Obj.magic
                 (Obj.repr
                    (if
                       FStar_Order.le
                         (FStar_Reflection_V2_Compare.compare_term t t')
                     then
                       Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> t :: ts))
                     else
                       Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Pure.fst"
                                     (Prims.of_int (482)) (Prims.of_int (13))
                                     (Prims.of_int (482)) (Prims.of_int (26)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Pure.fst"
                                     (Prims.of_int (482)) (Prims.of_int (9))
                                     (Prims.of_int (482)) (Prims.of_int (26)))))
                            (Obj.magic (insert1 t ts'))
                            (fun uu___1 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 -> t' :: uu___1)))))) uu___1
        uu___
let (sort_terms :
  Pulse_Syntax_Base.term Prims.list ->
    (Pulse_Syntax_Base.term Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  = fun ts -> FStar_Tactics_Util.fold_right insert1 ts []
let (canon_vprop_list_print :
  Pulse_Syntax_Base.term Prims.list ->
    (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun vs ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Pure.fst"
               (Prims.of_int (491)) (Prims.of_int (21)) (Prims.of_int (491))
               (Prims.of_int (34)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Pure.fst"
               (Prims.of_int (491)) (Prims.of_int (4)) (Prims.of_int (491))
               (Prims.of_int (34))))) (Obj.magic (sort_terms vs))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> list_as_vprop uu___))
let (canon_vprop_print :
  Pulse_Syntax_Base.term ->
    (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  = fun vp -> canon_vprop_list_print (vprop_as_list vp)