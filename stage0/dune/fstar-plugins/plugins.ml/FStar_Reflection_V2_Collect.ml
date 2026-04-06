open Fstarcompiler
open Prims
let rec inspect_ln_unascribe (t : FStarC_Reflection_Types.term) :
  FStarC_Reflection_V2_Data.term_view=
  match FStarC_Reflection_V2_Builtins.inspect_ln t with
  | FStarC_Reflection_V2_Data.Tv_AscribedT (t', uu___, uu___1, uu___2) ->
      inspect_ln_unascribe t'
  | FStarC_Reflection_V2_Data.Tv_AscribedC (t', uu___, uu___1, uu___2) ->
      inspect_ln_unascribe t'
  | tv -> tv
let rec collect_app_ln' (args : FStarC_Reflection_V2_Data.argv Prims.list)
  (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.term * FStarC_Reflection_V2_Data.argv Prims.list)=
  match inspect_ln_unascribe t with
  | FStarC_Reflection_V2_Data.Tv_App (l, r) -> collect_app_ln' (r :: args) l
  | uu___ -> (t, args)
let collect_app_ln :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.term * FStarC_Reflection_V2_Data.argv
      Prims.list)=
  collect_app_ln' []
let rec collect_arr' (bs : FStarC_Reflection_Types.binder Prims.list)
  (c : FStarC_Reflection_Types.comp) :
  (FStarC_Reflection_Types.binder Prims.list * FStarC_Reflection_Types.comp)=
  match FStarC_Reflection_V2_Builtins.inspect_comp c with
  | FStarC_Reflection_V2_Data.C_Total t ->
      (match inspect_ln_unascribe t with
       | FStarC_Reflection_V2_Data.Tv_Arrow (b, c1) ->
           collect_arr' (b :: bs) c1
       | uu___ -> (bs, c))
  | uu___ -> (bs, c)
let collect_arr_ln_bs (t : FStarC_Reflection_Types.typ) :
  (FStarC_Reflection_Types.binder Prims.list * FStarC_Reflection_Types.comp)=
  let uu___ =
    collect_arr' []
      (FStarC_Reflection_V2_Builtins.pack_comp
         (FStarC_Reflection_V2_Data.C_Total t)) in
  match uu___ with | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)
let collect_arr_ln (t : FStarC_Reflection_Types.typ) :
  (FStarC_Reflection_Types.typ Prims.list * FStarC_Reflection_Types.comp)=
  let uu___ = collect_arr_ln_bs t in
  match uu___ with
  | (bs, c) ->
      ((FStar_List_Tot_Base.map
          (fun b ->
             (FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2)
          bs), c)
let rec collect_abs' (bs : FStarC_Reflection_Types.binder Prims.list)
  (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.binder Prims.list * FStarC_Reflection_Types.term)=
  match inspect_ln_unascribe t with
  | FStarC_Reflection_V2_Data.Tv_Abs (b, t') -> collect_abs' (b :: bs) t'
  | uu___ -> (bs, t)
let collect_abs_ln (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.binder Prims.list * FStarC_Reflection_Types.term)=
  let uu___ = collect_abs' [] t in
  match uu___ with | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')
