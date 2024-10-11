open Prims
let (join_goals : Prims.bool) = false
let (debug_flag :
  Prims.string -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun s ->
    let uu___ = FStarC_Tactics_V2_Builtins.ext_getv (Prims.strcat "pulse:" s) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Config.fst" (Prims.of_int (25))
               (Prims.of_int (10)) (Prims.of_int (25)) (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Config.fst" (Prims.of_int (26))
               (Prims.of_int (2)) (Prims.of_int (26)) (Prims.of_int (37)))))
      (Obj.magic uu___)
      (fun v ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> ((v <> "") && (v <> "0")) && (v <> "false")))