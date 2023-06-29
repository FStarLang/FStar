open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (prover : Pulse_Prover_Common.prover_t) =
  fun uu___ ->
    fun uu___1 ->
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> Prims.magic ()))
let (prove_precondition :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
                 (unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3 FStar_Pervasives_Native.option,
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
                     fun t ->
                       fun c ->
                         fun t_typing ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> Prims.magic ()))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___