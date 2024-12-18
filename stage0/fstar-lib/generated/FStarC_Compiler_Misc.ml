open Prims
let (compare_version :
  Prims.string -> Prims.string -> FStarC_Compiler_Order.order) =
  fun v1 ->
    fun v2 ->
      let cs1 =
        FStarC_Compiler_List.map FStarC_Compiler_Util.int_of_string
          (FStarC_Compiler_String.split [46] v1) in
      let cs2 =
        FStarC_Compiler_List.map FStarC_Compiler_Util.int_of_string
          (FStarC_Compiler_String.split [46] v2) in
      FStarC_Compiler_Order.compare_list cs1 cs2
        FStarC_Compiler_Order.compare_int
let (version_gt : Prims.string -> Prims.string -> Prims.bool) =
  fun v1 ->
    fun v2 ->
      let uu___ = compare_version v1 v2 in uu___ = FStarC_Compiler_Order.Gt
let (version_ge : Prims.string -> Prims.string -> Prims.bool) =
  fun v1 ->
    fun v2 ->
      let uu___ = compare_version v1 v2 in uu___ <> FStarC_Compiler_Order.Lt