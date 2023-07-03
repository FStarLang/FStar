open Prims
let (should_elim_exists :
  Pulse_Syntax_Base.vprop -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun v ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match v.Pulse_Syntax_Base.t with
               | Pulse_Syntax_Base.Tm_ExistsSL (uu___1, uu___2, uu___3) ->
                   true
               | uu___1 -> false))) uu___
let (mk :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        ((Pulse_Syntax_Base.ppname, Pulse_Syntax_Base.st_term,
           Pulse_Syntax_Base.comp, (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple4 FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun v ->
             fun v_typing ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       match v.Pulse_Syntax_Base.t with
                       | Pulse_Syntax_Base.Tm_ExistsSL
                           (u,
                            { Pulse_Syntax_Base.binder_ty = t;
                              Pulse_Syntax_Base.binder_ppname = nm;_},
                            p)
                           ->
                           FStar_Pervasives_Native.Some
                             (FStar_Pervasives.Mkdtuple4
                                (nm,
                                  (Pulse_Typing.wr
                                     (Pulse_Syntax_Base.Tm_ElimExists
                                        {
                                          Pulse_Syntax_Base.p1 =
                                            (Pulse_Syntax_Base.tm_exists_sl
                                               (Pulse_Syntax_Base.comp_u
                                                  (Pulse_Typing.comp_elim_exists
                                                     u t p
                                                     (nm,
                                                       (Pulse_Typing_Env.fresh
                                                          g))))
                                               (Pulse_Typing.as_binder t) p)
                                        })),
                                  (Pulse_Typing.comp_elim_exists u t p
                                     (nm, (Pulse_Typing_Env.fresh g))),
                                  (Pulse_Typing.T_ElimExists
                                     (g,
                                       (Pulse_Syntax_Base.comp_u
                                          (Pulse_Typing.comp_elim_exists u t
                                             p
                                             (nm, (Pulse_Typing_Env.fresh g)))),
                                       t, p, (Pulse_Typing_Env.fresh g), (),
                                       ()))))
                       | uu___1 -> FStar_Pervasives_Native.None))) uu___2
          uu___1 uu___
let (elim_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        ((Pulse_Typing_Env.env, Pulse_Syntax_Base.term, unit,
           (unit, unit, unit, unit)
             Pulse_Prover_Common.continuation_elaborator)
           FStar_Pervasives.dtuple4,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Prover.ElimExists.fst"
                   (Prims.of_int (39)) (Prims.of_int (70))
                   (Prims.of_int (39)) (Prims.of_int (78)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Prover.ElimExists.fst"
                   (Prims.of_int (39)) (Prims.of_int (81))
                   (Prims.of_int (43)) (Prims.of_int (62)))))
          (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))
          (fun uu___ ->
             (fun ctxt_emp_typing ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Prover.ElimExists.fst"
                              (Prims.of_int (40)) (Prims.of_int (45))
                              (Prims.of_int (40)) (Prims.of_int (92)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Prover.ElimExists.fst"
                              (Prims.of_int (39)) (Prims.of_int (81))
                              (Prims.of_int (43)) (Prims.of_int (62)))))
                     (Obj.magic
                        (Pulse_Prover_Common.add_elims g ctxt
                           Pulse_Syntax_Base.tm_emp should_elim_exists mk ()))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 ->
                             match uu___ with
                             | FStar_Pervasives.Mkdtuple4
                                 (g', ctxt', ctxt'_emp_typing, k) ->
                                 FStar_Pervasives.Mkdtuple4
                                   (g', ctxt', (),
                                     (Pulse_Prover_Common.k_elab_equiv g g'
                                        (Pulse_Syntax_Base.tm_star ctxt
                                           Pulse_Syntax_Base.tm_emp) ctxt
                                        (Pulse_Syntax_Base.tm_star ctxt'
                                           Pulse_Syntax_Base.tm_emp) ctxt' k
                                        () ())))))) uu___)
let (elim_exists_pst :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      (unit Pulse_Prover_Common.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun preamble ->
         fun pst ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Prims.admit ())))
        uu___1 uu___