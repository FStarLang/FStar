open Prims
type check_t =
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
            ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
               (unit, unit, unit) Pulse_Typing.st_typing)
               FStar_Pervasives.dtuple3,
              unit) FStar_Tactics_Effect.tac_repr