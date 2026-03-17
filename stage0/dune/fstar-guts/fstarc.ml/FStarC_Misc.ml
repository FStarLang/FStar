open Prims
let compare_version (v1 : Prims.string) (v2 : Prims.string) :
  FStarC_Order.order=
  let cs1 =
    FStarC_List.map FStarC_Util.int_of_string (FStarC_String.split [46] v1) in
  let cs2 =
    FStarC_List.map FStarC_Util.int_of_string (FStarC_String.split [46] v2) in
  FStarC_Order.compare_list cs1 cs2 FStarC_Order.compare_int
let version_gt (v1 : Prims.string) (v2 : Prims.string) : Prims.bool=
  let uu___ = compare_version v1 v2 in uu___ = FStarC_Order.Gt
let version_ge (v1 : Prims.string) (v2 : Prims.string) : Prims.bool=
  let uu___ = compare_version v1 v2 in uu___ <> FStarC_Order.Lt
