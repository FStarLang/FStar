open Prims
type 'a termable =
  {
  to_term:
    'a -> (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr }
let __proj__Mktermable__item__to_term :
  'a .
    'a termable ->
      'a ->
        (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr
  = fun projectee -> match projectee with | { to_term;_} -> to_term
let to_term :
  'a .
    'a termable ->
      'a ->
        (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr
  =
  fun projectee -> match projectee with | { to_term = to_term1;_} -> to_term1
let (termable_term : FStarC_Reflection_Types.term termable) =
  {
    to_term =
      (fun uu___ ->
         (fun t ->
            Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           uu___)
  }
let (termable_binding : FStarC_Reflection_V2_Data.binding termable) =
  {
    to_term =
      (fun uu___ ->
         (fun b ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    FStar_Tactics_V2_SyntaxCoercions.binding_to_term b)))
           uu___)
  }
let mapply :
  'ty . 'ty termable -> 'ty -> (unit, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    fun x ->
      let uu___1 = to_term uu___ x in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.MApply.fsti"
                 (Prims.of_int (23)) (Prims.of_int (10)) (Prims.of_int (23))
                 (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.MApply.fsti"
                 (Prims.of_int (24)) (Prims.of_int (2)) (Prims.of_int (24))
                 (Prims.of_int (11))))) (Obj.magic uu___1)
        (fun uu___2 ->
           (fun t -> Obj.magic (FStar_Tactics_MApply0.mapply0 t)) uu___2)