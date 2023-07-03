open Prims
let (prove :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              ((Pulse_Typing_Env.env, Pulse_Prover_Substs.t,
                 Pulse_Syntax_Base.vprop,
                 (unit, unit, unit, unit)
                   Pulse_Prover_Common.continuation_elaborator)
                 FStar_Pervasives.dtuple4,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun ctxt ->
                   fun ctxt_typing ->
                     fun uvs ->
                       fun goals ->
                         fun goals_typing ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> Prims.admit ()))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___