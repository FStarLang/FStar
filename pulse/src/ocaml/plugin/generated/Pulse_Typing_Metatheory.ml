open Prims

let (st_typing_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Typing_Env.env -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun g' ->
      fun t ->
        fun c ->
          fun d ->
            fun g1 ->
              let g2 = Pulse_Typing_Env.diff g1 g in
              let d1 =
                Pulse_Typing_Metatheory_Base.st_typing_weakening g g' t c d
                  g2 in
              d1
let (st_typing_weakening_standard :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Typing_Env.env -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          fun g1 ->
            let g' = Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env g) in
            let d1 = st_typing_weakening g g' t c d g1 in d1
let (st_typing_weakening_end :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Typing_Env.env -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun g' ->
      fun t ->
        fun c ->
          fun d ->
            fun g'' ->
              let g2 = Pulse_Typing_Env.diff g'' g' in
              let emp_env =
                Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env g) in
              let d1 =
                Pulse_Typing_Metatheory_Base.st_typing_weakening
                  (Pulse_Typing_Env.push_env g g') emp_env t c
                  (FStar_Pervasives.coerce_eq () d) g2 in
              FStar_Pervasives.coerce_eq () d1