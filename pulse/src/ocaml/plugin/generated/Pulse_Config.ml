open Prims
let (join_goals : Prims.bool) = false
let (debug_flag :
  Prims.string -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun s ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Config.fst" (Prims.of_int (9))
               (Prims.of_int (10)) (Prims.of_int (9)) (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Config.fst" (Prims.of_int (10))
               (Prims.of_int (2)) (Prims.of_int (10)) (Prims.of_int (37)))))
      (Obj.magic
         (FStar_Tactics_V2_Builtins.ext_getv (Prims.strcat "pulse:" s)))
      (fun v ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> ((v <> "") && (v <> "0")) && (v <> "false")))