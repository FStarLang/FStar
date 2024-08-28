open Prims
let rec (inspect_ln_unascribe :
  FStar_Reflection_Types.term -> FStar_Reflection_V2_Data.term_view) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_AscribedT (t', uu___, uu___1, uu___2) ->
        inspect_ln_unascribe t'
    | FStar_Reflection_V2_Data.Tv_AscribedC (t', uu___, uu___1, uu___2) ->
        inspect_ln_unascribe t'
    | tv -> tv
let rec (collect_app_ln' :
  FStar_Reflection_V2_Data.argv Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term * FStar_Reflection_V2_Data.argv
        Prims.list))
  =
  fun args ->
    fun t ->
      match inspect_ln_unascribe t with
      | FStar_Reflection_V2_Data.Tv_App (l, r) ->
          collect_app_ln' (r :: args) l
      | uu___ -> (t, args)
let (collect_app_ln :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term * FStar_Reflection_V2_Data.argv Prims.list))
  = collect_app_ln' []
let rec (collect_arr' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.binder Prims.list *
        FStar_Reflection_Types.comp))
  =
  fun bs ->
    fun c ->
      match FStar_Reflection_V2_Builtins.inspect_comp c with
      | FStar_Reflection_V2_Data.C_Total t ->
          (match inspect_ln_unascribe t with
           | FStar_Reflection_V2_Data.Tv_Arrow (b, c1) ->
               collect_arr' (b :: bs) c1
           | uu___ -> (bs, c))
      | uu___ -> (bs, c)
let (collect_arr_ln_bs :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.comp))
  =
  fun t ->
    let uu___ =
      collect_arr' []
        (FStar_Reflection_V2_Builtins.pack_comp
           (FStar_Reflection_V2_Data.C_Total t)) in
    match uu___ with | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)
let (collect_arr_ln :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.typ Prims.list * FStar_Reflection_Types.comp))
  =
  fun t ->
    let uu___ = collect_arr_ln_bs t in
    match uu___ with
    | (bs, c) ->
        ((FStar_List_Tot_Base.map
            (fun b ->
               (FStar_Reflection_V2_Builtins.inspect_binder b).FStar_Reflection_V2_Data.sort2)
            bs), c)
let rec (collect_abs' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.binder Prims.list *
        FStar_Reflection_Types.term))
  =
  fun bs ->
    fun t ->
      match inspect_ln_unascribe t with
      | FStar_Reflection_V2_Data.Tv_Abs (b, t') -> collect_abs' (b :: bs) t'
      | uu___ -> (bs, t)
let (collect_abs_ln :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.term))
  =
  fun t ->
    let uu___ = collect_abs' [] t in
    match uu___ with | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')