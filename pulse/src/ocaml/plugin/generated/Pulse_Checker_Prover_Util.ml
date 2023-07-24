open Prims
let (st_typing_subst :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp_st ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Checker_Prover_Substs.ss_t ->
              ((unit, unit, unit) Pulse_Typing.st_typing
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun t ->
        fun c ->
          fun d ->
            fun ss ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.Util.fst"
                         (Prims.of_int (16)) (Prims.of_int (16))
                         (Prims.of_int (16)) (Prims.of_int (43)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.Util.fst"
                         (Prims.of_int (17)) (Prims.of_int (2))
                         (Prims.of_int (24)) (Prims.of_int (10)))))
                (Obj.magic
                   (Pulse_Checker_Prover_Substs.ss_to_nt_substs g uvs ss))
                (fun nts_opt ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        match nts_opt with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some nts ->
                            FStar_Pervasives_Native.Some
                              (Pulse_Checker_Prover_Substs.st_typing_nt_substs
                                 g uvs
                                 (Pulse_Typing_Env.mk_env
                                    (Pulse_Typing_Env.fstar_env g)) t c d nts)))
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
                Pulse_Typing_Metatheory.st_typing_weakening g g' t c d g2 in
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
                Pulse_Typing_Metatheory.st_typing_weakening
                  (Pulse_Typing_Env.push_env g g') emp_env t c
                  (FStar_Pervasives.coerce_eq () d) g2 in
              FStar_Pervasives.coerce_eq () d1
let (debug_prover :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun uu___ ->
         fun uu___1 ->
           Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ())))
        uu___1 uu___