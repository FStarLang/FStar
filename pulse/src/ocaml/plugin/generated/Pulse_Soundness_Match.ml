open Prims
let (complete_soundness :
  Pulse_Soundness_Common.stt_env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.branch Prims.list ->
            Pulse_Syntax_Base.comp_st ->
              (unit, unit, unit, unit, unit, unit) Pulse_Typing.brs_typing ->
                (unit, unit, unit, unit) Pulse_Typing.pats_complete ->
                  FStar_Reflection_V2_Data.binding Prims.list Prims.list ->
                    (unit, unit, unit, unit, unit)
                      FStar_Reflection_Typing.match_is_complete)
  =
  fun g ->
    fun sc_u ->
      fun sc_ty ->
        fun sc ->
          fun brs ->
            fun c ->
              fun d ->
                fun comp ->
                  fun bs ->
                    let uu___ = comp in
                    match uu___ with
                    | Pulse_Typing.PC_Elab
                        (uu___1, uu___2, uu___3, uu___4, bs', s) -> s