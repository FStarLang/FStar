open Prims
let (namedv_to_term :
  FStar_Tactics_NamedView.namedv -> FStar_Tactics_NamedView.term) =
  fun x -> FStar_Tactics_NamedView.pack (FStar_Tactics_NamedView.Tv_Var x)
let (binder_to_namedv :
  FStar_Tactics_NamedView.binder -> FStar_Tactics_NamedView.namedv) =
  fun b ->
    {
      FStarC_Reflection_V2_Data.uniq = (b.FStar_Tactics_NamedView.uniq);
      FStarC_Reflection_V2_Data.sort =
        (FStar_Sealed.seal b.FStar_Tactics_NamedView.sort);
      FStarC_Reflection_V2_Data.ppname = (b.FStar_Tactics_NamedView.ppname)
    }
let (binder_to_term :
  FStar_Tactics_NamedView.binder -> FStar_Tactics_NamedView.term) =
  fun b ->
    FStar_Tactics_NamedView.pack
      (FStar_Tactics_NamedView.Tv_Var (binder_to_namedv b))
let (binding_to_namedv :
  FStar_Tactics_NamedView.binding -> FStar_Tactics_NamedView.namedv) =
  fun b ->
    {
      FStarC_Reflection_V2_Data.uniq = (b.FStarC_Reflection_V2_Data.uniq1);
      FStarC_Reflection_V2_Data.sort =
        (FStar_Sealed.seal b.FStarC_Reflection_V2_Data.sort3);
      FStarC_Reflection_V2_Data.ppname =
        (b.FStarC_Reflection_V2_Data.ppname3)
    }
let (binding_to_term :
  FStar_Tactics_NamedView.binding -> FStar_Tactics_NamedView.term) =
  fun x -> namedv_to_term (binding_to_namedv x)