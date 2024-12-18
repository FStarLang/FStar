open Prims
let (bv_of_binder :
  FStarC_Reflection_Types.binder -> FStarC_Reflection_Types.bv) =
  fun b ->
    (FStarC_Reflection_V1_Builtins.inspect_binder b).FStarC_Reflection_V1_Data.binder_bv
let rec (inspect_ln_unascribe :
  FStarC_Reflection_Types.term -> FStarC_Reflection_V1_Data.term_view) =
  fun t ->
    match FStarC_Reflection_V1_Builtins.inspect_ln t with
    | FStarC_Reflection_V1_Data.Tv_AscribedT (t', uu___, uu___1, uu___2) ->
        inspect_ln_unascribe t'
    | FStarC_Reflection_V1_Data.Tv_AscribedC (t', uu___, uu___1, uu___2) ->
        inspect_ln_unascribe t'
    | tv -> tv
let (mk_binder :
  FStarC_Reflection_Types.bv ->
    FStarC_Reflection_Types.typ -> FStarC_Reflection_Types.binder)
  =
  fun bv ->
    fun sort ->
      FStarC_Reflection_V1_Builtins.pack_binder
        {
          FStarC_Reflection_V1_Data.binder_bv = bv;
          FStarC_Reflection_V1_Data.binder_qual =
            FStarC_Reflection_V1_Data.Q_Explicit;
          FStarC_Reflection_V1_Data.binder_attrs = [];
          FStarC_Reflection_V1_Data.binder_sort = sort
        }
let (mk_implicit_binder :
  FStarC_Reflection_Types.bv ->
    FStarC_Reflection_Types.typ -> FStarC_Reflection_Types.binder)
  =
  fun bv ->
    fun sort ->
      FStarC_Reflection_V1_Builtins.pack_binder
        {
          FStarC_Reflection_V1_Data.binder_bv = bv;
          FStarC_Reflection_V1_Data.binder_qual =
            FStarC_Reflection_V1_Data.Q_Implicit;
          FStarC_Reflection_V1_Data.binder_attrs = [];
          FStarC_Reflection_V1_Data.binder_sort = sort
        }
let (type_of_binder :
  FStarC_Reflection_Types.binder -> FStarC_Reflection_Types.typ) =
  fun b ->
    (FStarC_Reflection_V1_Builtins.inspect_binder b).FStarC_Reflection_V1_Data.binder_sort
let rec (flatten_name : FStarC_Reflection_Types.name -> Prims.string) =
  fun ns ->
    match ns with
    | [] -> ""
    | n::[] -> n
    | n::ns1 -> Prims.strcat n (Prims.strcat "." (flatten_name ns1))
let rec (collect_app_ln' :
  FStarC_Reflection_V1_Data.argv Prims.list ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term * FStarC_Reflection_V1_Data.argv
        Prims.list))
  =
  fun args ->
    fun t ->
      match inspect_ln_unascribe t with
      | FStarC_Reflection_V1_Data.Tv_App (l, r) ->
          collect_app_ln' (r :: args) l
      | uu___ -> (t, args)
let (collect_app_ln :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.term * FStarC_Reflection_V1_Data.argv
      Prims.list))
  = collect_app_ln' []
let rec (mk_app :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_V1_Data.argv Prims.list -> FStarC_Reflection_Types.term)
  =
  fun t ->
    fun args ->
      match args with
      | [] -> t
      | x::xs ->
          mk_app
            (FStarC_Reflection_V1_Builtins.pack_ln
               (FStarC_Reflection_V1_Data.Tv_App (t, x))) xs
let (mk_e_app :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term Prims.list -> FStarC_Reflection_Types.term)
  =
  fun t ->
    fun args ->
      let e t1 = (t1, FStarC_Reflection_V1_Data.Q_Explicit) in
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
          FStarC_Reflection_V1_Builtins.pack_ln
            (FStarC_Reflection_V1_Data.Tv_Arrow
               (b,
                 (FStarC_Reflection_V1_Builtins.pack_comp
                    (FStarC_Reflection_V1_Data.C_Total
                       (mk_tot_arr_ln bs1 cod)))))
let rec (collect_arr' :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.comp ->
      (FStarC_Reflection_Types.binder Prims.list *
        FStarC_Reflection_Types.comp))
  =
  fun bs ->
    fun c ->
      match FStarC_Reflection_V1_Builtins.inspect_comp c with
      | FStarC_Reflection_V1_Data.C_Total t ->
          (match inspect_ln_unascribe t with
           | FStarC_Reflection_V1_Data.Tv_Arrow (b, c1) ->
               collect_arr' (b :: bs) c1
           | uu___ -> (bs, c))
      | uu___ -> (bs, c)
let (collect_arr_ln_bs :
  FStarC_Reflection_Types.typ ->
    (FStarC_Reflection_Types.binder Prims.list *
      FStarC_Reflection_Types.comp))
  =
  fun t ->
    let uu___ =
      collect_arr' []
        (FStarC_Reflection_V1_Builtins.pack_comp
           (FStarC_Reflection_V1_Data.C_Total t)) in
    match uu___ with | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)
let (collect_arr_ln :
  FStarC_Reflection_Types.typ ->
    (FStarC_Reflection_Types.typ Prims.list * FStarC_Reflection_Types.comp))
  =
  fun t ->
    let uu___ = collect_arr_ln_bs t in
    match uu___ with
    | (bs, c) -> ((FStar_List_Tot_Base.map type_of_binder bs), c)
let rec (collect_abs' :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.binder Prims.list *
        FStarC_Reflection_Types.term))
  =
  fun bs ->
    fun t ->
      match inspect_ln_unascribe t with
      | FStarC_Reflection_V1_Data.Tv_Abs (b, t') -> collect_abs' (b :: bs) t'
      | uu___ -> (bs, t)
let (collect_abs_ln :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.binder Prims.list *
      FStarC_Reflection_Types.term))
  =
  fun t ->
    let uu___ = collect_abs' [] t in
    match uu___ with | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')
let (fv_to_string : FStarC_Reflection_Types.fv -> Prims.string) =
  fun fv ->
    FStarC_Reflection_V1_Builtins.implode_qn
      (FStarC_Reflection_V1_Builtins.inspect_fv fv)
let (mk_stringlit : Prims.string -> FStarC_Reflection_Types.term) =
  fun s ->
    FStarC_Reflection_V1_Builtins.pack_ln
      (FStarC_Reflection_V1_Data.Tv_Const
         (FStarC_Reflection_V1_Data.C_String s))
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
        (FStarC_Reflection_V1_Builtins.pack_ln
           (FStarC_Reflection_V1_Data.Tv_FVar
              (FStarC_Reflection_V1_Builtins.pack_fv
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
          (FStarC_Reflection_V1_Builtins.pack_ln
             (FStarC_Reflection_V1_Data.Tv_FVar
                (FStarC_Reflection_V1_Builtins.pack_fv
                   FStar_Reflection_Const.cons_qn)))
          [(ty, FStarC_Reflection_V1_Data.Q_Implicit);
          (h, FStarC_Reflection_V1_Data.Q_Explicit);
          (t, FStarC_Reflection_V1_Data.Q_Explicit)]
let rec (mk_list :
  FStarC_Reflection_Types.term Prims.list -> FStarC_Reflection_Types.term) =
  fun ts ->
    match ts with
    | [] ->
        FStarC_Reflection_V1_Builtins.pack_ln
          (FStarC_Reflection_V1_Data.Tv_FVar
             (FStarC_Reflection_V1_Builtins.pack_fv
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
          (FStarC_Reflection_V1_Builtins.pack_ln
             (FStarC_Reflection_V1_Data.Tv_FVar
                (FStarC_Reflection_V1_Builtins.pack_fv qn))) ts
let (destruct_tuple :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term Prims.list FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = collect_app_ln t in
    match uu___ with
    | (head, args) ->
        (match FStarC_Reflection_V1_Builtins.inspect_ln head with
         | FStarC_Reflection_V1_Data.Tv_FVar fv ->
             if
               FStar_List_Tot_Base.mem
                 (FStarC_Reflection_V1_Builtins.inspect_fv fv)
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
                            | FStarC_Reflection_V1_Data.Q_Explicit -> [t1]
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
    match FStarC_Reflection_V1_Builtins.inspect_ln t with
    | FStarC_Reflection_V1_Data.Tv_Match (t1, uu___, uu___1) -> head t1
    | FStarC_Reflection_V1_Data.Tv_Let
        (uu___, uu___1, uu___2, uu___3, t1, uu___4) -> head t1
    | FStarC_Reflection_V1_Data.Tv_Abs (uu___, t1) -> head t1
    | FStarC_Reflection_V1_Data.Tv_Refine (uu___, uu___1, t1) -> head t1
    | FStarC_Reflection_V1_Data.Tv_App (t1, uu___) -> head t1
    | FStarC_Reflection_V1_Data.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
        head t1
    | FStarC_Reflection_V1_Data.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
        head t1
    | FStarC_Reflection_V1_Data.Tv_Unknown -> t
    | FStarC_Reflection_V1_Data.Tv_Uvar (uu___, uu___1) -> t
    | FStarC_Reflection_V1_Data.Tv_Const uu___ -> t
    | FStarC_Reflection_V1_Data.Tv_Type uu___ -> t
    | FStarC_Reflection_V1_Data.Tv_Var uu___ -> t
    | FStarC_Reflection_V1_Data.Tv_BVar uu___ -> t
    | FStarC_Reflection_V1_Data.Tv_FVar uu___ -> t
    | FStarC_Reflection_V1_Data.Tv_UInst (uu___, uu___1) -> t
    | FStarC_Reflection_V1_Data.Tv_Arrow (uu___, uu___1) -> t
    | FStarC_Reflection_V1_Data.Tv_Unsupp -> t
let (is_fvar : FStarC_Reflection_Types.term -> Prims.string -> Prims.bool) =
  fun t ->
    fun nm ->
      match inspect_ln_unascribe t with
      | FStarC_Reflection_V1_Data.Tv_FVar fv ->
          (FStarC_Reflection_V1_Builtins.implode_qn
             (FStarC_Reflection_V1_Builtins.inspect_fv fv))
            = nm
      | FStarC_Reflection_V1_Data.Tv_UInst (fv, uu___) ->
          (FStarC_Reflection_V1_Builtins.implode_qn
             (FStarC_Reflection_V1_Builtins.inspect_fv fv))
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
    match FStarC_Reflection_V1_Builtins.inspect_ln (head t) with
    | FStarC_Reflection_V1_Data.Tv_Uvar (uu___, uu___1) -> true
    | uu___ -> false
let (binder_set_qual :
  FStarC_Reflection_V1_Data.aqualv ->
    FStarC_Reflection_Types.binder -> FStarC_Reflection_Types.binder)
  =
  fun q ->
    fun b ->
      let bview = FStarC_Reflection_V1_Builtins.inspect_binder b in
      FStarC_Reflection_V1_Builtins.pack_binder
        {
          FStarC_Reflection_V1_Data.binder_bv =
            (bview.FStarC_Reflection_V1_Data.binder_bv);
          FStarC_Reflection_V1_Data.binder_qual = q;
          FStarC_Reflection_V1_Data.binder_attrs =
            (bview.FStarC_Reflection_V1_Data.binder_attrs);
          FStarC_Reflection_V1_Data.binder_sort =
            (bview.FStarC_Reflection_V1_Data.binder_sort)
        }
let (add_check_with :
  FStarC_VConfig.vconfig ->
    FStarC_Reflection_Types.sigelt -> FStarC_Reflection_Types.sigelt)
  =
  fun vcfg ->
    fun se ->
      let attrs = FStarC_Reflection_V1_Builtins.sigelt_attrs se in
      let vcfg_t = FStarC_Reflection_V1_Builtins.embed_vconfig vcfg in
      let t =
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_App
             ((FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "Stubs"; "VConfig"; "check_with"]))),
               (vcfg_t, FStarC_Reflection_V2_Data.Q_Explicit))) in
      FStarC_Reflection_V1_Builtins.set_sigelt_attrs (t :: attrs) se
let (un_uinst : FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun t ->
    match FStarC_Reflection_V1_Builtins.inspect_ln t with
    | FStarC_Reflection_V1_Data.Tv_UInst (fv, uu___) ->
        FStarC_Reflection_V1_Builtins.pack_ln
          (FStarC_Reflection_V1_Data.Tv_FVar fv)
    | uu___ -> t
let rec (is_name_imp :
  FStarC_Reflection_Types.name -> FStarC_Reflection_Types.term -> Prims.bool)
  =
  fun nm ->
    fun t ->
      match inspect_ln_unascribe t with
      | FStarC_Reflection_V1_Data.Tv_FVar fv ->
          if (FStarC_Reflection_V1_Builtins.inspect_fv fv) = nm
          then true
          else false
      | FStarC_Reflection_V1_Data.Tv_UInst (fv, uu___) ->
          if (FStarC_Reflection_V1_Builtins.inspect_fv fv) = nm
          then true
          else false
      | FStarC_Reflection_V1_Data.Tv_App
          (l, (uu___, FStarC_Reflection_V1_Data.Q_Implicit)) ->
          is_name_imp nm l
      | uu___ -> false
let (unsquash_term :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match inspect_ln_unascribe t with
    | FStarC_Reflection_V1_Data.Tv_App
        (l, (r, FStarC_Reflection_V1_Data.Q_Explicit)) ->
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