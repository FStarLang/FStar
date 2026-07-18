open Fstarcompiler
open Prims
type 'a termable =
  {
  to_term:
    'a -> (FStarC_Reflection_Types.term, Obj.t) FStar_Tactics_Effect.tac_repr }
let __proj__Mktermable__item__to_term (projectee : 'a termable) :
  'a -> (FStarC_Reflection_Types.term, Obj.t) FStar_Tactics_Effect.tac_repr=
  match projectee with | { to_term;_} -> to_term
let to_term (projectee : 'a termable) :
  'a -> (FStarC_Reflection_Types.term, Obj.t) FStar_Tactics_Effect.tac_repr=
  match projectee with | { to_term = to_term1;_} -> to_term1
let termable_term : FStarC_Reflection_Types.term termable=
  { to_term = (fun t uu___ -> t) }
let termable_binding : FStarC_Reflection_V2_Data.binding termable=
  {
    to_term =
      (fun b uu___ -> FStar_Tactics_V2_SyntaxCoercions.binding_to_term b)
  }
let mapply (uu___ : 'ty termable) (x : 'ty) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x1 = to_term uu___ x ps in FStar_Tactics_MApply0.mapply0 x1 ps
