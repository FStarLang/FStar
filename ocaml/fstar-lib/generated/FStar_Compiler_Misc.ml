open Prims
let (compare_version : Prims.string -> Prims.string -> FStar_Order.order) =
  fun v1 ->
    fun v2 ->
      let cs1 =
        FStar_Compiler_Effect.op_Bar_Greater
          (FStar_Compiler_String.split [46] v1)
          (FStar_Compiler_List.map FStar_Compiler_Util.int_of_string) in
      let cs2 =
        FStar_Compiler_Effect.op_Bar_Greater
          (FStar_Compiler_String.split [46] v2)
          (FStar_Compiler_List.map FStar_Compiler_Util.int_of_string) in
      FStar_Order.compare_list cs1 cs2 FStar_Order.compare_int
let (version_gt : Prims.string -> Prims.string -> Prims.bool) =
  fun v1 ->
    fun v2 -> let uu___ = compare_version v1 v2 in uu___ = FStar_Order.Gt
let (version_ge : Prims.string -> Prims.string -> Prims.bool) =
  fun v1 ->
    fun v2 -> let uu___ = compare_version v1 v2 in uu___ <> FStar_Order.Lt