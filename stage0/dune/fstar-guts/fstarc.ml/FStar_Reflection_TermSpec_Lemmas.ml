open Prims
let open_with_var_elt_spec (x : FStarC_Reflection_V2_Data.var)
  (i : Prims.nat) : FStar_Reflection_TermSpec.subst_spec_elt=
  FStar_Reflection_TermSpec.DTs (i, ())
let open_with_var_spec (x : FStarC_Reflection_V2_Data.var) (i : Prims.nat) :
  FStar_Reflection_TermSpec.subst_spec= [open_with_var_elt_spec x i]
