open Prims
let rec denote_flags (fs : FStarC_Reflection_V2_Data.cflag Prims.list) :
  unit Prims.list=
  match fs with | [] -> [] | f::fs1 -> () :: (denote_flags fs1)
type subst_spec = unit


