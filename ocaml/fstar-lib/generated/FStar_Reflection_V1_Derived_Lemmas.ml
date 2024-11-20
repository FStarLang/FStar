open Prims
type ('a, 'p, 'l) forall_list = Obj.t
type ('a, 'p, 'l) forallP = unit
type ('a, 'r, 'l, 'r1) op_Less_Less_Colon = unit
let rec list_ref : 'a 'p . 'a Prims.list -> 'a Prims.list =
  fun l -> match l with | [] -> [] | x::xs -> x :: (list_ref xs)
let (collect_app_ref :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.term * FStarC_Reflection_V1_Data.argv
      Prims.list))
  =
  fun t ->
    let uu___ = FStar_Reflection_V1_Derived.collect_app_ln t in
    match uu___ with | (h, a) -> (h, (list_ref a))
let (collect_abs_ln_ref :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.binder Prims.list *
      FStarC_Reflection_Types.term))
  =
  fun t ->
    let uu___ = FStar_Reflection_V1_Derived.collect_abs_ln t in
    match uu___ with | (bds, body) -> ((list_ref bds), body)
let (collect_arr_ln_bs_ref :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.binder Prims.list *
      FStarC_Reflection_Types.comp))
  =
  fun t ->
    let uu___ = FStar_Reflection_V1_Derived.collect_arr_ln_bs t in
    match uu___ with | (bds, c) -> ((list_ref bds), c)