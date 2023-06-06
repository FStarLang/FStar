open Prims
let (intro_exists : Pulse_Checker_Auto_Util.intro_from_unmatched_fn) =
  fun g ->
    fun uu___ ->
      fun p ->
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStar_Pervasives_Native.None))