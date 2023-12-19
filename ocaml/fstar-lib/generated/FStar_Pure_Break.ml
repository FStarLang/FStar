open Prims
type 'p break_wp' = unit FStar_Pervasives.spinoff
let (post : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Pure.Break.fsti" (Prims.of_int (12))
               (Prims.of_int (2)) (Prims.of_int (12)) (Prims.of_int (46)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Pure.Break.fsti" (Prims.of_int (13))
               (Prims.of_int (2)) (Prims.of_int (13)) (Prims.of_int (9)))))
      (Obj.magic
         (FStar_Tactics_V2_Builtins.norm
            [FStar_Pervasives.delta_fully
               ["FStar.Pure.Break.mono_lem"; "FStar.Pure.Break.break_wp'"]]))
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_V2_Derived.trefl ())) uu___1)
type 'p break_wp = unit FStar_Pervasives.spinoff