open Prims
type check_t =
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        Pulse_Syntax.term ->
          unit ->
            Pulse_Syntax.term FStar_Pervasives_Native.option ->
              ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                 (unit, unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr