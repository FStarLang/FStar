open Prims
let (type_of_binder :
  FStarC_Reflection_Types.binder -> FStarC_Reflection_Types.typ) =
  fun b ->
    (FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2
let rec (inspect_ln_unascribe :
  FStarC_Reflection_Types.term -> FStarC_Reflection_V2_Data.term_view) =
  fun t ->
    match FStarC_Reflection_V2_Builtins.inspect_ln t with
    | FStarC_Reflection_V2_Data.Tv_AscribedT (t', uu___, uu___1, uu___2) ->
        inspect_ln_unascribe t'
    | FStarC_Reflection_V2_Data.Tv_AscribedC (t', uu___, uu___1, uu___2) ->
        inspect_ln_unascribe t'
    | tv -> tv
let (compare_bv :
  FStarC_Reflection_Types.bv ->
    FStarC_Reflection_Types.bv -> FStar_Order.order)
  =
  fun v1 ->
    fun v2 ->
      FStar_Order.compare_int
        (FStarC_Reflection_V2_Builtins.inspect_bv v1).FStarC_Reflection_V2_Data.index
        (FStarC_Reflection_V2_Builtins.inspect_bv v2).FStarC_Reflection_V2_Data.index
let (compare_namedv :
  FStarC_Reflection_Types.namedv ->
    FStarC_Reflection_Types.namedv -> FStar_Order.order)
  =
  fun v1 ->
    fun v2 ->
      FStar_Order.compare_int
        (FStarC_Reflection_V2_Builtins.inspect_namedv v1).FStarC_Reflection_V2_Data.uniq
        (FStarC_Reflection_V2_Builtins.inspect_namedv v2).FStarC_Reflection_V2_Data.uniq
let (shift :
  Prims.int ->
    FStarC_Syntax_Syntax.subst_elt -> FStarC_Syntax_Syntax.subst_elt)
  =
  fun n ->
    fun s ->
      match s with
      | FStarC_Syntax_Syntax.DB (i, t) ->
          FStarC_Syntax_Syntax.DB ((i + n), t)
      | FStarC_Syntax_Syntax.DT (i, t) ->
          FStarC_Syntax_Syntax.DT ((i + n), t)
      | FStarC_Syntax_Syntax.UN (i, t) ->
          FStarC_Syntax_Syntax.UN ((i + n), t)
      | FStarC_Syntax_Syntax.NM (x, i) ->
          FStarC_Syntax_Syntax.NM (x, (i + n))
      | FStarC_Syntax_Syntax.UD (x, i) ->
          FStarC_Syntax_Syntax.UD (x, (i + n))
      | FStarC_Syntax_Syntax.NT (uu___, uu___1) -> s
let (shift_subst :
  Prims.int ->
    FStarC_Syntax_Syntax.subst_elt Prims.list ->
      FStarC_Syntax_Syntax.subst_elt Prims.list)
  = fun n -> fun s -> FStar_List_Tot_Base.map (shift n) s
let (subst1 :
  FStarC_Reflection_Types.namedv ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun n ->
    fun t1 ->
      fun t2 ->
        FStarC_Reflection_V2_Builtins.subst_term
          [FStarC_Syntax_Syntax.NT (n, t1)] t2
let (mk_binder :
  Prims.string ->
    FStarC_Reflection_Types.typ -> FStarC_Reflection_V2_Data.simple_binder)
  =
  fun nm ->
    fun sort ->
      let bv =
        {
          FStarC_Reflection_V2_Data.sort2 = sort;
          FStarC_Reflection_V2_Data.qual =
            FStarC_Reflection_V2_Data.Q_Explicit;
          FStarC_Reflection_V2_Data.attrs = [];
          FStarC_Reflection_V2_Data.ppname2 = (FStar_Sealed.seal nm)
        } in
      FStarC_Reflection_V2_Builtins.pack_binder bv
let (mk_implicit_binder :
  Prims.string ->
    FStarC_Reflection_Types.typ -> FStarC_Reflection_Types.binder)
  =
  fun nm ->
    fun sort ->
      FStarC_Reflection_V2_Builtins.pack_binder
        {
          FStarC_Reflection_V2_Data.sort2 = sort;
          FStarC_Reflection_V2_Data.qual =
            FStarC_Reflection_V2_Data.Q_Implicit;
          FStarC_Reflection_V2_Data.attrs = [];
          FStarC_Reflection_V2_Data.ppname2 = (FStar_Sealed.seal nm)
        }
let (push_binding :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_V2_Data.binding -> FStarC_Reflection_Types.env)
  =
  fun e ->
    fun b ->
      let nv =
        FStarC_Reflection_V2_Builtins.pack_namedv
          {
            FStarC_Reflection_V2_Data.uniq =
              (b.FStarC_Reflection_V2_Data.uniq1);
            FStarC_Reflection_V2_Data.sort =
              (FStar_Sealed.seal b.FStarC_Reflection_V2_Data.sort3);
            FStarC_Reflection_V2_Data.ppname =
              (b.FStarC_Reflection_V2_Data.ppname3)
          } in
      FStarC_Reflection_V2_Builtins.push_namedv e nv
let rec (flatten_name : FStarC_Reflection_Types.name -> Prims.string) =
  fun ns ->
    match ns with
    | [] -> ""
    | n::[] -> n
    | n::ns1 -> Prims.strcat n (Prims.strcat "." (flatten_name ns1))
let rec (mk_app :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_V2_Data.argv Prims.list -> FStarC_Reflection_Types.term)
  =
  fun t ->
    fun args ->
      match args with
      | [] -> t
      | x::xs ->
          mk_app
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_App (t, x))) xs
let (mk_e_app :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term Prims.list -> FStarC_Reflection_Types.term)
  =
  fun t ->
    fun args ->
      let e t1 = (t1, FStarC_Reflection_V2_Data.Q_Explicit) in
      mk_app t (FStar_List_Tot_Base.map e args)
let (u_unk : FStarC_Reflection_Types.universe) =
  FStarC_Reflection_V2_Builtins.pack_universe
    FStarC_Reflection_V2_Data.Uv_Unk
let rec (mk_tot_arr_ln :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> cod
      | b::bs1 ->
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Arrow
               (b,
                 (FStarC_Reflection_V2_Builtins.pack_comp
                    (FStarC_Reflection_V2_Data.C_Total
                       (mk_tot_arr_ln bs1 cod)))))
let rec (mk_arr_ln :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.comp -> FStarC_Reflection_Types.term)
  =
  fun bs ->
    fun cod ->
      match bs with
      | b::[] ->
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Arrow (b, cod))
      | b::bs1 ->
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_Arrow
               (b,
                 (FStarC_Reflection_V2_Builtins.pack_comp
                    (FStarC_Reflection_V2_Data.C_Total (mk_arr_ln bs1 cod)))))
let (fv_to_string : FStarC_Reflection_Types.fv -> Prims.string) =
  fun fv ->
    FStarC_Reflection_V2_Builtins.implode_qn
      (FStarC_Reflection_V2_Builtins.inspect_fv fv)
let (mk_stringlit : Prims.string -> FStarC_Reflection_Types.term) =
  fun s ->
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_Const
         (FStarC_Reflection_V2_Data.C_String s))
let (mk_strcat :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun t1 ->
    fun t2 ->
      mk_e_app
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "strcat"])))
        [t1; t2]
let (mk_cons :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun h ->
    fun t ->
      mk_e_app
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 FStar_Reflection_Const.cons_qn))) [h; t]
let (mk_cons_t :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun ty ->
    fun h ->
      fun t ->
        mk_app
          (FStarC_Reflection_V2_Builtins.pack_ln
             (FStarC_Reflection_V2_Data.Tv_FVar
                (FStarC_Reflection_V2_Builtins.pack_fv
                   FStar_Reflection_Const.cons_qn)))
          [(ty, FStarC_Reflection_V2_Data.Q_Implicit);
          (h, FStarC_Reflection_V2_Data.Q_Explicit);
          (t, FStarC_Reflection_V2_Data.Q_Explicit)]
let rec (mk_list :
  FStarC_Reflection_Types.term Prims.list -> FStarC_Reflection_Types.term) =
  fun ts ->
    match ts with
    | [] ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                FStar_Reflection_Const.nil_qn))
    | t::ts1 -> mk_cons t (mk_list ts1)
let (mktuple_n :
  FStarC_Reflection_Types.term Prims.list -> FStarC_Reflection_Types.term) =
  fun ts ->
    match FStar_List_Tot_Base.length ts with
    | uu___ when uu___ = Prims.int_zero ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_Const
             FStarC_Reflection_V2_Data.C_Unit)
    | uu___ when uu___ = Prims.int_one ->
        let uu___1 = ts in (match uu___1 with | x::[] -> x)
    | n ->
        let qn =
          match n with
          | uu___ when uu___ = (Prims.of_int (2)) ->
              FStar_Reflection_Const.mktuple2_qn
          | uu___ when uu___ = (Prims.of_int (3)) ->
              FStar_Reflection_Const.mktuple3_qn
          | uu___ when uu___ = (Prims.of_int (4)) ->
              FStar_Reflection_Const.mktuple4_qn
          | uu___ when uu___ = (Prims.of_int (5)) ->
              FStar_Reflection_Const.mktuple5_qn
          | uu___ when uu___ = (Prims.of_int (6)) ->
              FStar_Reflection_Const.mktuple6_qn
          | uu___ when uu___ = (Prims.of_int (7)) ->
              FStar_Reflection_Const.mktuple7_qn
          | uu___ when uu___ = (Prims.of_int (8)) ->
              FStar_Reflection_Const.mktuple8_qn in
        mk_e_app
          (FStarC_Reflection_V2_Builtins.pack_ln
             (FStarC_Reflection_V2_Data.Tv_FVar
                (FStarC_Reflection_V2_Builtins.pack_fv qn))) ts
let (destruct_tuple :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term Prims.list FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = FStar_Reflection_V2_Collect.collect_app_ln t in
    match uu___ with
    | (head, args) ->
        (match FStarC_Reflection_V2_Builtins.inspect_ln head with
         | FStarC_Reflection_V2_Data.Tv_FVar fv ->
             if
               FStar_List_Tot_Base.mem
                 (FStarC_Reflection_V2_Builtins.inspect_fv fv)
                 [FStar_Reflection_Const.mktuple2_qn;
                 FStar_Reflection_Const.mktuple3_qn;
                 FStar_Reflection_Const.mktuple4_qn;
                 FStar_Reflection_Const.mktuple5_qn;
                 FStar_Reflection_Const.mktuple6_qn;
                 FStar_Reflection_Const.mktuple7_qn;
                 FStar_Reflection_Const.mktuple8_qn]
             then
               FStar_Pervasives_Native.Some
                 (FStar_List_Tot_Base.concatMap
                    (fun uu___1 ->
                       match uu___1 with
                       | (t1, q) ->
                           (match q with
                            | FStarC_Reflection_V2_Data.Q_Explicit -> [t1]
                            | uu___2 -> [])) args)
             else FStar_Pervasives_Native.None
         | uu___1 -> FStar_Pervasives_Native.None)
let (mkpair :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  = fun t1 -> fun t2 -> mktuple_n [t1; t2]
let rec (head : FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun t ->
    match FStarC_Reflection_V2_Builtins.inspect_ln t with
    | FStarC_Reflection_V2_Data.Tv_Match (t1, uu___, uu___1) -> head t1
    | FStarC_Reflection_V2_Data.Tv_Let (uu___, uu___1, uu___2, t1, uu___3) ->
        head t1
    | FStarC_Reflection_V2_Data.Tv_Abs (uu___, t1) -> head t1
    | FStarC_Reflection_V2_Data.Tv_Refine (uu___, t1) -> head t1
    | FStarC_Reflection_V2_Data.Tv_App (t1, uu___) -> head t1
    | FStarC_Reflection_V2_Data.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
        head t1
    | FStarC_Reflection_V2_Data.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
        head t1
    | FStarC_Reflection_V2_Data.Tv_Unknown -> t
    | FStarC_Reflection_V2_Data.Tv_Uvar (uu___, uu___1) -> t
    | FStarC_Reflection_V2_Data.Tv_Const uu___ -> t
    | FStarC_Reflection_V2_Data.Tv_Type uu___ -> t
    | FStarC_Reflection_V2_Data.Tv_Var uu___ -> t
    | FStarC_Reflection_V2_Data.Tv_BVar uu___ -> t
    | FStarC_Reflection_V2_Data.Tv_FVar uu___ -> t
    | FStarC_Reflection_V2_Data.Tv_UInst (uu___, uu___1) -> t
    | FStarC_Reflection_V2_Data.Tv_Arrow (uu___, uu___1) -> t
    | FStarC_Reflection_V2_Data.Tv_Unsupp -> t
let (is_fvar : FStarC_Reflection_Types.term -> Prims.string -> Prims.bool) =
  fun t ->
    fun nm ->
      match inspect_ln_unascribe t with
      | FStarC_Reflection_V2_Data.Tv_FVar fv ->
          (FStarC_Reflection_V2_Builtins.implode_qn
             (FStarC_Reflection_V2_Builtins.inspect_fv fv))
            = nm
      | FStarC_Reflection_V2_Data.Tv_UInst (fv, uu___) ->
          (FStarC_Reflection_V2_Builtins.implode_qn
             (FStarC_Reflection_V2_Builtins.inspect_fv fv))
            = nm
      | uu___ -> false
let rec (is_any_fvar :
  FStarC_Reflection_Types.term -> Prims.string Prims.list -> Prims.bool) =
  fun t ->
    fun nms ->
      match nms with
      | [] -> false
      | v::vs -> (is_fvar t v) || (is_any_fvar t vs)
let (is_uvar : FStarC_Reflection_Types.term -> Prims.bool) =
  fun t ->
    match FStarC_Reflection_V2_Builtins.inspect_ln (head t) with
    | FStarC_Reflection_V2_Data.Tv_Uvar (uu___, uu___1) -> true
    | uu___ -> false
let (binder_set_qual :
  FStarC_Reflection_V2_Data.aqualv ->
    FStarC_Reflection_Types.binder -> FStarC_Reflection_Types.binder)
  =
  fun q ->
    fun b ->
      let bview = FStarC_Reflection_V2_Builtins.inspect_binder b in
      FStarC_Reflection_V2_Builtins.pack_binder
        {
          FStarC_Reflection_V2_Data.sort2 =
            (bview.FStarC_Reflection_V2_Data.sort2);
          FStarC_Reflection_V2_Data.qual = q;
          FStarC_Reflection_V2_Data.attrs =
            (bview.FStarC_Reflection_V2_Data.attrs);
          FStarC_Reflection_V2_Data.ppname2 =
            (bview.FStarC_Reflection_V2_Data.ppname2)
        }
let (add_check_with :
  FStarC_VConfig.vconfig ->
    FStarC_Reflection_Types.sigelt -> FStarC_Reflection_Types.sigelt)
  =
  fun vcfg ->
    fun se ->
      let attrs = FStarC_Reflection_V2_Builtins.sigelt_attrs se in
      let vcfg_t = FStarC_Reflection_V2_Builtins.embed_vconfig vcfg in
      let t =
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_App
             ((FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "Stubs"; "VConfig"; "check_with"]))),
               (vcfg_t, FStarC_Reflection_V2_Data.Q_Explicit))) in
      FStarC_Reflection_V2_Builtins.set_sigelt_attrs (t :: attrs) se
let (un_uinst : FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun t ->
    match FStarC_Reflection_V2_Builtins.inspect_ln t with
    | FStarC_Reflection_V2_Data.Tv_UInst (fv, uu___) ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar fv)
    | uu___ -> t
let rec (is_name_imp :
  FStarC_Reflection_Types.name -> FStarC_Reflection_Types.term -> Prims.bool)
  =
  fun nm ->
    fun t ->
      match inspect_ln_unascribe t with
      | FStarC_Reflection_V2_Data.Tv_FVar fv ->
          if (FStarC_Reflection_V2_Builtins.inspect_fv fv) = nm
          then true
          else false
      | FStarC_Reflection_V2_Data.Tv_UInst (fv, uu___) ->
          if (FStarC_Reflection_V2_Builtins.inspect_fv fv) = nm
          then true
          else false
      | FStarC_Reflection_V2_Data.Tv_App
          (l, (uu___, FStarC_Reflection_V2_Data.Q_Implicit)) ->
          is_name_imp nm l
      | uu___ -> false
let (unsquash_term :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match inspect_ln_unascribe t with
    | FStarC_Reflection_V2_Data.Tv_App
        (l, (r, FStarC_Reflection_V2_Data.Q_Explicit)) ->
        if is_name_imp FStar_Reflection_Const.squash_qn l
        then FStar_Pervasives_Native.Some r
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let (maybe_unsquash_term :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term) =
  fun t ->
    match unsquash_term t with
    | FStar_Pervasives_Native.Some t' -> t'
    | FStar_Pervasives_Native.None -> t