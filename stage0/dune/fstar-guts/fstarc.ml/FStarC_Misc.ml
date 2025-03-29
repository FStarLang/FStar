open Prims
let (compare_version : Prims.string -> Prims.string -> FStarC_Order.order) =
  fun v1 ->
    fun v2 ->
      let cs1 =
        FStarC_List.map FStarC_Util.int_of_string
          (FStarC_String.split [46] v1) in
      let cs2 =
        FStarC_List.map FStarC_Util.int_of_string
          (FStarC_String.split [46] v2) in
      FStarC_Order.compare_list cs1 cs2 FStarC_Order.compare_int
let (version_gt : Prims.string -> Prims.string -> Prims.bool) =
  fun v1 ->
    fun v2 -> let uu___ = compare_version v1 v2 in uu___ = FStarC_Order.Gt
let (version_ge : Prims.string -> Prims.string -> Prims.bool) =
  fun v1 ->
    fun v2 -> let uu___ = compare_version v1 v2 in uu___ <> FStarC_Order.Lt
