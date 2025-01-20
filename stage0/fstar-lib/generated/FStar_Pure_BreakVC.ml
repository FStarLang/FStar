open Prims
type 'p break_wp' = unit FStar_Pervasives.spinoff
let (post : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      FStarC_Tactics_V2_Builtins.norm
        [FStar_Pervasives.delta_fully
           ["FStar.Pure.BreakVC.mono_lem"; "FStar.Pure.BreakVC.break_wp'"]] in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Pure.BreakVC.fsti"
               (Prims.of_int (12)) (Prims.of_int (2)) (Prims.of_int (12))
               (Prims.of_int (46)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Pure.BreakVC.fsti"
               (Prims.of_int (13)) (Prims.of_int (2)) (Prims.of_int (13))
               (Prims.of_int (9))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 -> Obj.magic (FStar_Tactics_V2_Derived.trefl ())) uu___2)
type 'p break_wp = unit FStar_Pervasives.spinoff
type ('p, 'q) op_Equals_Equals_Greater_Greater = unit