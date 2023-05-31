open Prims
let (should_elim_exists :
  Pulse_Syntax_Base.vprop -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun v ->
       match v with
       | Pulse_Syntax_Base.Tm_ExistsSL (uu___, uu___1, uu___2, s) ->
           Obj.magic (Obj.repr (FStar_Tactics_Builtins.unseal s))
       | uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false))))
      uu___
let (mk :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
           (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple3 FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun v ->
             fun v_typing ->
               match v with
               | Pulse_Syntax_Base.Tm_ExistsSL (u, t, p, s) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "Pulse.Checker.Auto.ElimExists.fst"
                              (Prims.of_int (22)) (Prims.of_int (7))
                              (Prims.of_int (22)) (Prims.of_int (17)))
                           (FStar_Range.mk_range
                              "Pulse.Checker.Auto.ElimExists.fst"
                              (Prims.of_int (22)) (Prims.of_int (4))
                              (Prims.of_int (29)) (Prims.of_int (13)))
                           (Obj.magic (FStar_Tactics_Builtins.unseal s))
                           (fun uu___ ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   if uu___
                                   then
                                     FStar_Pervasives_Native.Some
                                       (FStar_Pervasives.Mkdtuple3
                                          ((Pulse_Typing.wr
                                              (Pulse_Syntax_Base.Tm_ElimExists
                                                 {
                                                   Pulse_Syntax_Base.p =
                                                     (Pulse_Syntax_Base.Tm_ExistsSL
                                                        ((Pulse_Syntax_Base.comp_u
                                                            (Pulse_Typing.comp_elim_exists
                                                               u t p
                                                               (Pulse_Typing.fresh
                                                                  g))), t, p,
                                                          Pulse_Syntax_Base.should_elim_false))
                                                 })),
                                            (Pulse_Typing.comp_elim_exists u
                                               t p (Pulse_Typing.fresh g)),
                                            (Pulse_Typing.T_ElimExists
                                               (g,
                                                 (Pulse_Syntax_Base.comp_u
                                                    (Pulse_Typing.comp_elim_exists
                                                       u t p
                                                       (Pulse_Typing.fresh g))),
                                                 t, p,
                                                 (Pulse_Typing.fresh g), (),
                                                 ()))))
                                   else FStar_Pervasives_Native.None))))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> FStar_Pervasives_Native.None))))
          uu___2 uu___1 uu___
let (elim_exists :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        ((Pulse_Typing.env, Pulse_Syntax_Base.term, unit,
           (unit, unit, unit, unit)
             Pulse_Checker_Common.continuation_elaborator)
           FStar_Pervasives.dtuple4,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        Pulse_Checker_Auto_Util.add_elims g ctxt should_elim_exists mk ()