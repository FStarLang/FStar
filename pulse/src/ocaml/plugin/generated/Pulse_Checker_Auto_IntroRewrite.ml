open Prims
let (intro_rewrite : Pulse_Checker_Auto_Util.intro_from_unmatched_fn) =
  fun g ->
    fun p ->
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> FStar_Pervasives_Native.None))