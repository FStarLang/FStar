open Prims
let rec (mk_bind :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.term ->
        Pulse_Syntax.st_term ->
          Pulse_Syntax.st_term ->
            Pulse_Syntax.comp_st ->
              Pulse_Syntax.comp_st ->
                Pulse_Syntax.var ->
                  (unit, unit, unit, unit) Pulse_Typing.st_typing ->
                    unit ->
                      (unit, unit, unit, unit) Pulse_Typing.st_typing ->
                        unit ->
                          unit ->
                            ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                               (unit, unit, unit, unit)
                                 Pulse_Typing.st_typing)
                               FStar_Pervasives.dtuple3,
                              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___12 ->
    fun uu___11 ->
      fun uu___10 ->
        fun uu___9 ->
          fun uu___8 ->
            fun uu___7 ->
              fun uu___6 ->
                fun uu___5 ->
                  fun uu___4 ->
                    fun uu___3 ->
                      fun uu___2 ->
                        fun uu___1 ->
                          fun uu___ ->
                            (fun f ->
                               fun g ->
                                 fun pre ->
                                   fun e1 ->
                                     fun e2 ->
                                       fun c1 ->
                                         fun c2 ->
                                           fun x ->
                                             fun d_e1 ->
                                               fun d_c1res ->
                                                 fun d_e2 ->
                                                   fun res_typing ->
                                                     fun post_typing ->
                                                       match (c1, c2) with
                                                       | (Pulse_Syntax.C_ST
                                                          uu___,
                                                          Pulse_Syntax.C_ST
                                                          uu___1) ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax.Tm_Bind
                                                                    (e1, e2)),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, x,
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2),
                                                                    d_e1, (),
                                                                    d_e2,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    c1, c2,
                                                                    (), x,
                                                                    ()))))))))
                                                       | (Pulse_Syntax.C_STGhost
                                                          (inames1, uu___),
                                                          Pulse_Syntax.C_STGhost
                                                          (inames2, uu___1))
                                                           ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (if
                                                                   Pulse_Syntax.eq_tm
                                                                    inames1
                                                                    inames2
                                                                 then
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax.Tm_Bind
                                                                    (e1, e2)),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, x,
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2),
                                                                    d_e1, (),
                                                                    d_e2,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    c1, c2,
                                                                    (), x,
                                                                    ()))))))
                                                                 else
                                                                   FStar_Tactics_Derived.fail
                                                                    "Cannot compose two stghost computations with different opened invariants"))
                                                       | (Pulse_Syntax.C_STAtomic
                                                          (inames, uu___),
                                                          Pulse_Syntax.C_ST
                                                          uu___1) ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (if
                                                                   Pulse_Syntax.eq_tm
                                                                    inames
                                                                    Pulse_Syntax.Tm_EmpInames
                                                                 then
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax.Tm_Bind
                                                                    (e1, e2)),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax.C_ST
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c1)) c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2,
                                                                    (Pulse_Syntax.C_ST
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c1)), c2,
                                                                    x,
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax.C_ST
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c1)) c2),
                                                                    (Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    (Pulse_Syntax.C_ST
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c1)),
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g, c1)))),
                                                                    (), d_e2,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    (Pulse_Syntax.C_ST
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c1)), c2,
                                                                    (), x,
                                                                    ()))))))
                                                                 else
                                                                   FStar_Tactics_Derived.fail
                                                                    "Cannot compose atomic with non-emp opened invariants with stt"))
                                                       | (Pulse_Syntax.C_STGhost
                                                          (inames1, uu___),
                                                          Pulse_Syntax.C_STAtomic
                                                          (inames2, uu___1))
                                                           ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (if
                                                                   Pulse_Syntax.eq_tm
                                                                    inames1
                                                                    inames2
                                                                 then
                                                                   Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (71)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (73)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.get_non_informative_witness
                                                                    f g
                                                                    (Pulse_Syntax.comp_u
                                                                    c1)
                                                                    (Pulse_Syntax.comp_res
                                                                    c1)))
                                                                    (fun w ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax.Tm_Bind
                                                                    (e1, e2)),
                                                                    (Pulse_Typing.bind_comp_ghost_l_out
                                                                    c1 c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, x,
                                                                    (Pulse_Typing.bind_comp_ghost_l_out
                                                                    c1 c2),
                                                                    d_e1, (),
                                                                    d_e2,
                                                                    (Pulse_Typing.Bind_comp_ghost_l
                                                                    (g, x,
                                                                    c1, c2,
                                                                    w, (), x,
                                                                    ()))))))))
                                                                 else
                                                                   Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Cannot compose ghost and atomic with different opened invariants")))
                                                       | (Pulse_Syntax.C_STAtomic
                                                          (inames1, uu___),
                                                          Pulse_Syntax.C_STGhost
                                                          (inames2, uu___1))
                                                           ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (if
                                                                   Pulse_Syntax.eq_tm
                                                                    inames1
                                                                    inames2
                                                                 then
                                                                   Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (71)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (73)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.get_non_informative_witness
                                                                    f g
                                                                    (Pulse_Syntax.comp_u
                                                                    c2)
                                                                    (Pulse_Syntax.comp_res
                                                                    c2)))
                                                                    (fun w ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax.Tm_Bind
                                                                    (e1, e2)),
                                                                    (Pulse_Typing.bind_comp_ghost_r_out
                                                                    c1 c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, x,
                                                                    (Pulse_Typing.bind_comp_ghost_r_out
                                                                    c1 c2),
                                                                    d_e1, (),
                                                                    d_e2,
                                                                    (Pulse_Typing.Bind_comp_ghost_r
                                                                    (g, x,
                                                                    c1, c2,
                                                                    w, (), x,
                                                                    ()))))))))
                                                                 else
                                                                   Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Cannot compose atomic and ghost with different opened invariants")))
                                                       | (Pulse_Syntax.C_ST
                                                          uu___,
                                                          Pulse_Syntax.C_STAtomic
                                                          (inames, uu___1))
                                                           ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (if
                                                                   Pulse_Syntax.eq_tm
                                                                    inames
                                                                    Pulse_Syntax.Tm_EmpInames
                                                                 then
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax.Tm_Bind
                                                                    (e1, e2)),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1
                                                                    (Pulse_Syntax.C_ST
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c2))),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    (Pulse_Syntax.C_ST
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c2)), x,
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1
                                                                    (Pulse_Syntax.C_ST
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c2))),
                                                                    d_e1, (),
                                                                    (Pulse_Typing.T_Lift
                                                                    (((x,
                                                                    (FStar_Pervasives.Inl
                                                                    (Pulse_Syntax.comp_res
                                                                    c1))) ::
                                                                    g),
                                                                    (Pulse_Syntax.open_st_term
                                                                    e2 x),
                                                                    c2,
                                                                    (Pulse_Syntax.C_ST
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c2)),
                                                                    d_e2,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (((x,
                                                                    (FStar_Pervasives.Inl
                                                                    (Pulse_Syntax.comp_res
                                                                    c1))) ::
                                                                    g), c2)))),
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    c1,
                                                                    (Pulse_Syntax.C_ST
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c2)), (),
                                                                    x, ()))))))
                                                                 else
                                                                   FStar_Tactics_Derived.fail
                                                                    "Cannot compose stt with atomic with non-emp opened invariants"))
                                                       | (Pulse_Syntax.C_STGhost
                                                          (inames, uu___),
                                                          Pulse_Syntax.C_ST
                                                          uu___1) ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (if
                                                                   Pulse_Syntax.eq_tm
                                                                    inames
                                                                    Pulse_Syntax.Tm_EmpInames
                                                                 then
                                                                   Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (71)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (82)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.get_non_informative_witness
                                                                    f g
                                                                    (Pulse_Syntax.comp_u
                                                                    c1)
                                                                    (Pulse_Syntax.comp_res
                                                                    c1)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun w ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (82)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax.C_STAtomic
                                                                    (inames,
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c1))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    c1lifted
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (82)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    c1lifted,
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_STGhost_STAtomic
                                                                    (g, c1,
                                                                    w)))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    f g pre
                                                                    e1 e2
                                                                    c1lifted
                                                                    c2 x
                                                                    d_e11 ()
                                                                    d_e2 ()
                                                                    ()))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2))
                                                                 else
                                                                   Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Cannot compose ghost with stt with non-emp opened invariants")))
                                                       | (Pulse_Syntax.C_ST
                                                          uu___,
                                                          Pulse_Syntax.C_STGhost
                                                          (inames, uu___1))
                                                           ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (if
                                                                   Pulse_Syntax.eq_tm
                                                                    inames
                                                                    Pulse_Syntax.Tm_EmpInames
                                                                 then
                                                                   Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (82)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (x,
                                                                    (FStar_Pervasives.Inl
                                                                    (Pulse_Syntax.comp_res
                                                                    c1))) ::
                                                                    g))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (72)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (82)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.get_non_informative_witness
                                                                    f g'
                                                                    (Pulse_Syntax.comp_u
                                                                    c2)
                                                                    (Pulse_Syntax.comp_res
                                                                    c2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun w ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (82)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax.C_STAtomic
                                                                    (inames,
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    c2lifted
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (82)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (((x,
                                                                    (FStar_Pervasives.Inl
                                                                    (Pulse_Syntax.comp_res
                                                                    c1))) ::
                                                                    g),
                                                                    (Pulse_Syntax.open_st_term
                                                                    e2 x),
                                                                    c2,
                                                                    c2lifted,
                                                                    d_e2,
                                                                    (Pulse_Typing.Lift_STGhost_STAtomic
                                                                    (g', c2,
                                                                    w)))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    d_e21 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    f g pre
                                                                    e1 e2 c1
                                                                    c2lifted
                                                                    x d_e1 ()
                                                                    d_e21 ()
                                                                    ()))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2))
                                                                 else
                                                                   Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Cannot compose stt with ghost with non-emp opened invariants")))
                                                       | (Pulse_Syntax.C_STAtomic
                                                          (inames, uu___),
                                                          Pulse_Syntax.C_STAtomic
                                                          (uu___1, uu___2))
                                                           ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (if
                                                                   Pulse_Syntax.eq_tm
                                                                    inames
                                                                    Pulse_Syntax.Tm_EmpInames
                                                                 then
                                                                   Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (82)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax.C_ST
                                                                    (Pulse_Syntax.st_comp_of_comp
                                                                    c1)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    c1lifted
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (82)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    c1lifted,
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g, c1)))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    f g pre
                                                                    e1 e2
                                                                    c1lifted
                                                                    c2 x
                                                                    d_e11 ()
                                                                    d_e2 ()
                                                                    ()))
                                                                    uu___3)))
                                                                    uu___3))
                                                                 else
                                                                   Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Cannot compose statomics with non-emp opened invariants")))
                                                       | (uu___, uu___1) ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Derived.fail
                                                                   "bind either not implemented (e.g. ghost) or not possible")))
                              uu___12 uu___11 uu___10 uu___9 uu___8 uu___7
                              uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (check_bind :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.st_term ->
        Pulse_Syntax.term ->
          unit ->
            Pulse_Syntax.term FStar_Pervasives_Native.option ->
              Pulse_Checker_Common.check_t ->
                ((Pulse_Syntax.st_term, Pulse_Syntax.comp,
                   (unit, unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun check ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                     (Prims.of_int (132)) (Prims.of_int (22))
                     (Prims.of_int (132)) (Prims.of_int (23)))
                  (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                     (Prims.of_int (132)) (Prims.of_int (2))
                     (Prims.of_int (176)) (Prims.of_int (5)))
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | Pulse_Syntax.Tm_Bind (e1, e2) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Bind.fst"
                                    (Prims.of_int (133)) (Prims.of_int (25))
                                    (Prims.of_int (133)) (Prims.of_int (57)))
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Bind.fst"
                                    (Prims.of_int (133)) (Prims.of_int (2))
                                    (Prims.of_int (176)) (Prims.of_int (5)))
                                 (Obj.magic
                                    (check f g e1 pre ()
                                       FStar_Pervasives_Native.None))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       match uu___1 with
                                       | FStar_Pervasives.Mkdtuple3
                                           (e11, c1, d1) ->
                                           if Pulse_Syntax.uu___is_C_Tot c1
                                           then
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Derived.fail
                                                     "Bind: c1 is not st"))
                                           else
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Bind.fst"
                                                        (Prims.of_int (137))
                                                        (Prims.of_int (13))
                                                        (Prims.of_int (137))
                                                        (Prims.of_int (31)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Bind.fst"
                                                        (Prims.of_int (138))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (176))
                                                        (Prims.of_int (5)))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 ->
                                                           Pulse_Syntax.st_comp_of_comp
                                                             c1))
                                                     (fun uu___3 ->
                                                        (fun s1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Bind.fst"
                                                                   (Prims.of_int (138))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (138))
                                                                   (Prims.of_int (18)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Bind.fst"
                                                                   (Prims.of_int (139))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (176))
                                                                   (Prims.of_int (5)))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    s1.Pulse_Syntax.res))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun t1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    f g t1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u,
                                                                    t_typing)
                                                                    ->
                                                                    if
                                                                    u <>
                                                                    s1.Pulse_Syntax.u
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "incorrect universe"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (23)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax.open_term
                                                                    s1.Pulse_Syntax.post
                                                                    x))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    next_pre
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (x,
                                                                    (FStar_Pervasives.Inl
                                                                    (s1.Pulse_Syntax.res)))
                                                                    :: g))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    f g'
                                                                    next_pre))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    next_pre_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (97)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (check f
                                                                    g'
                                                                    (Pulse_Syntax.open_st_term
                                                                    e2 x)
                                                                    next_pre
                                                                    ()
                                                                    post_hint))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e2', c2,
                                                                    d2) ->
                                                                    if
                                                                    Pulse_Syntax.uu___is_C_Tot
                                                                    c2
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Bind: c2 is not st"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax.close_st_term
                                                                    e2' x))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    d2))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    d21))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d22
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax.st_comp_of_comp
                                                                    c2))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun s2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    f g
                                                                    s2.Pulse_Syntax.res))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u1,
                                                                    res_typing)
                                                                    ->
                                                                    if
                                                                    u1 <>
                                                                    s2.Pulse_Syntax.u
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Unexpected universe for result type"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax.freevars
                                                                    s2.Pulse_Syntax.post)
                                                                    then
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (121)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (121)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (120)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    s2.Pulse_Syntax.post))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Bound variable "
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    x)
                                                                    " escapes scope in postcondition "))
                                                                    (Prims.strcat
                                                                    uu___9 "")))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___9)
                                                                    else
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (86)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax.open_term
                                                                    s2.Pulse_Syntax.post
                                                                    x))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    s2_post_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (89)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (86)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    f
                                                                    ((x,
                                                                    (FStar_Pervasives.Inl
                                                                    (s2.Pulse_Syntax.res)))
                                                                    :: g)
                                                                    s2_post_opened))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    post_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    f g pre
                                                                    e11
                                                                    e2_closed
                                                                    c1 c2 x
                                                                    d1 () d22
                                                                    () ()))
                                                                    uu___10)))
                                                                    uu___10))))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7))))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                          uu___3)))) uu___1)))
                       uu___)