open Prims
let (nvar_as_binder :
  Pulse_Syntax_Base.nvar ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.binder)
  =
  fun x ->
    fun t ->
      {
        Pulse_Syntax_Base.binder_ty = t;
        Pulse_Syntax_Base.binder_ppname = (FStar_Pervasives_Native.fst x)
      }
let rec (mk_bind :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            Pulse_Syntax_Base.comp_st ->
              Pulse_Syntax_Base.nvar ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  unit ->
                    (unit, unit, unit) Pulse_Typing.st_typing ->
                      unit ->
                        unit ->
                          ((Pulse_Syntax_Base.st_term,
                             Pulse_Syntax_Base.comp,
                             (unit, unit, unit) Pulse_Typing.st_typing)
                             FStar_Pervasives.dtuple3,
                            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun e1 ->
        fun e2 ->
          fun c1 ->
            fun c2 ->
              fun px ->
                fun d_e1 ->
                  fun d_c1res ->
                    fun d_e2 ->
                      fun res_typing ->
                        fun post_typing ->
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                               (Prims.of_int (42)) (Prims.of_int (13))
                               (Prims.of_int (42)) (Prims.of_int (15)))
                            (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                               (Prims.of_int (41)) (Prims.of_int (38))
                               (Prims.of_int (122)) (Prims.of_int (77)))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> px))
                            (fun uu___ ->
                               (fun uu___ ->
                                  match uu___ with
                                  | (uu___1, x) ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Bind.fst"
                                              (Prims.of_int (43))
                                              (Prims.of_int (10))
                                              (Prims.of_int (43))
                                              (Prims.of_int (41)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Bind.fst"
                                              (Prims.of_int (44))
                                              (Prims.of_int (2))
                                              (Prims.of_int (122))
                                              (Prims.of_int (77)))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 nvar_as_binder px
                                                   (Pulse_Syntax_Base.comp_res
                                                      c1)))
                                           (fun uu___2 ->
                                              (fun b ->
                                                 match (c1, c2) with
                                                 | (Pulse_Syntax_Base.C_ST
                                                    uu___2,
                                                    Pulse_Syntax_Base.C_ST
                                                    uu___3) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___4 ->
                                                                FStar_Pervasives.Mkdtuple3
                                                                  ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (
                                                                    Pulse_Typing.bind_comp_out
                                                                    c1 c2),
                                                                    (
                                                                    Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2),
                                                                    d_e1, (),
                                                                    d_e2,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    c1, c2,
                                                                    (), x,
                                                                    ()))))))))
                                                 | (Pulse_Syntax_Base.C_STGhost
                                                    (inames1, uu___2),
                                                    Pulse_Syntax_Base.C_STGhost
                                                    (inames2, uu___3)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames1
                                                               inames2
                                                           then
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___4 ->
                                                                  FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1 c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
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
                                                 | (Pulse_Syntax_Base.C_STAtomic
                                                    (inames, uu___2),
                                                    Pulse_Syntax_Base.C_ST
                                                    uu___3) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames
                                                               Pulse_Syntax_Base.Tm_EmpInames
                                                           then
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___4 ->
                                                                  FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)) c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)), c2,
                                                                    b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)) c2),
                                                                    (Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)),
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g, c1)))),
                                                                    (), d_e2,
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)), c2,
                                                                    (), x,
                                                                    ()))))))
                                                           else
                                                             FStar_Tactics_Derived.fail
                                                               "Cannot compose atomic with non-emp opened invariants with stt"))
                                                 | (Pulse_Syntax_Base.C_STGhost
                                                    (inames1, uu___2),
                                                    Pulse_Syntax_Base.C_STAtomic
                                                    (inames2, uu___3)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames1
                                                               inames2
                                                           then
                                                             Obj.repr
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (69)))
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (63)))
                                                                  (Obj.magic
                                                                    (Pulse_Checker_Pure.get_non_informative_witness
                                                                    g
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c1)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)))
                                                                  (fun w ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_ghost_l_out
                                                                    c1 c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
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
                                                 | (Pulse_Syntax_Base.C_STAtomic
                                                    (inames1, uu___2),
                                                    Pulse_Syntax_Base.C_STGhost
                                                    (inames2, uu___3)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames1
                                                               inames2
                                                           then
                                                             Obj.repr
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (69)))
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (63)))
                                                                  (Obj.magic
                                                                    (Pulse_Checker_Pure.get_non_informative_witness
                                                                    g
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c2)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c2)))
                                                                  (fun w ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_ghost_r_out
                                                                    c1 c2),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    c2, b,
                                                                    (FStar_Pervasives_Native.snd
                                                                    px),
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
                                                 | (Pulse_Syntax_Base.C_ST
                                                    uu___2,
                                                    Pulse_Syntax_Base.C_STAtomic
                                                    (inames, uu___3)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames
                                                               Pulse_Syntax_Base.Tm_EmpInames
                                                           then
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___4 ->
                                                                  FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2))),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g, e1,
                                                                    e2, c1,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)), b,
                                                                    (match px
                                                                    with
                                                                    | 
                                                                    (_1, _2)
                                                                    -> _2),
                                                                    (Pulse_Typing.bind_comp_out
                                                                    c1
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2))),
                                                                    d_e1, (),
                                                                    (Pulse_Typing.T_Lift
                                                                    ((Pulse_Typing.extend
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives.Inl
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)) g),
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px),
                                                                    c2,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)),
                                                                    d_e2,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    ((Pulse_Typing.extend
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives.Inl
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)) g),
                                                                    c2)))),
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)), (),
                                                                    x, ()))))))
                                                           else
                                                             FStar_Tactics_Derived.fail
                                                               "Cannot compose stt with atomic with non-emp opened invariants"))
                                                 | (Pulse_Syntax_Base.C_STGhost
                                                    (inames, uu___2),
                                                    Pulse_Syntax_Base.C_ST
                                                    uu___3) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames
                                                               Pulse_Syntax_Base.Tm_EmpInames
                                                           then
                                                             Obj.repr
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (69)))
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (81)))
                                                                  (Obj.magic
                                                                    (Pulse_Checker_Pure.get_non_informative_witness
                                                                    g
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c1)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)))
                                                                  (fun uu___4
                                                                    ->
                                                                    (fun w ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (inames,
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    c1lifted
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    c1lifted,
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_STGhost_STAtomic
                                                                    (g, c1,
                                                                    w)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    c1lifted
                                                                    c2 px
                                                                    d_e11 ()
                                                                    d_e2 ()
                                                                    ()))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4))
                                                           else
                                                             Obj.repr
                                                               (FStar_Tactics_Derived.fail
                                                                  "Cannot compose ghost with stt with non-emp opened invariants")))
                                                 | (Pulse_Syntax_Base.C_ST
                                                    uu___2,
                                                    Pulse_Syntax_Base.C_STGhost
                                                    (inames, uu___3)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames
                                                               Pulse_Syntax_Base.Tm_EmpInames
                                                           then
                                                             Obj.repr
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (45)))
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (81)))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)) g))
                                                                  (fun uu___4
                                                                    ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (70)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (81)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.get_non_informative_witness
                                                                    g'
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c2)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c2)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun w ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (inames,
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    c2lifted
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.T_Lift
                                                                    ((Pulse_Typing.extend
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives.Inl
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)) g),
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px),
                                                                    c2,
                                                                    c2lifted,
                                                                    d_e2,
                                                                    (Pulse_Typing.Lift_STGhost_STAtomic
                                                                    (g', c2,
                                                                    w)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    d_e21 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2 c1
                                                                    c2lifted
                                                                    px d_e1
                                                                    () d_e21
                                                                    () ()))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4))
                                                           else
                                                             Obj.repr
                                                               (FStar_Tactics_Derived.fail
                                                                  "Cannot compose stt with ghost with non-emp opened invariants")))
                                                 | (Pulse_Syntax_Base.C_STAtomic
                                                    (inames, uu___2),
                                                    Pulse_Syntax_Base.C_STAtomic
                                                    (uu___3, uu___4)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames
                                                               Pulse_Syntax_Base.Tm_EmpInames
                                                           then
                                                             Obj.repr
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (46)))
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (81)))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)))
                                                                  (fun uu___5
                                                                    ->
                                                                    (fun
                                                                    c1lifted
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, e1,
                                                                    c1,
                                                                    c1lifted,
                                                                    d_e1,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g, c1)))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    d_e11 ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2
                                                                    c1lifted
                                                                    c2 px
                                                                    d_e11 ()
                                                                    d_e2 ()
                                                                    ()))
                                                                    uu___5)))
                                                                    uu___5))
                                                           else
                                                             Obj.repr
                                                               (FStar_Tactics_Derived.fail
                                                                  "Cannot compose statomics with non-emp opened invariants")))
                                                 | (uu___2, uu___3) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Derived.fail
                                                             "bind either not implemented (e.g. ghost) or not possible")))
                                                uu___2))) uu___)
let (check_bind :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
            Pulse_Checker_Common.check_t ->
              ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                 (unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun check ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                   (Prims.of_int (136)) (Prims.of_int (47))
                   (Prims.of_int (136)) (Prims.of_int (53)))
                (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                   (Prims.of_int (135)) (Prims.of_int (29))
                   (Prims.of_int (182)) (Prims.of_int (5)))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> t.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_Bind
                          { Pulse_Syntax_Base.binder = b;
                            Pulse_Syntax_Base.head1 = e1;
                            Pulse_Syntax_Base.body1 = e2;_}
                          ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                                  (Prims.of_int (137)) (Prims.of_int (25))
                                  (Prims.of_int (137)) (Prims.of_int (55)))
                               (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                                  (Prims.of_int (136)) (Prims.of_int (56))
                                  (Prims.of_int (182)) (Prims.of_int (5)))
                               (Obj.magic
                                  (check g e1 pre ()
                                     FStar_Pervasives_Native.None))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | FStar_Pervasives.Mkdtuple3
                                         (e11, c1, d1) ->
                                         if
                                           Pulse_Syntax_Base.uu___is_C_Tot c1
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
                                                      (Prims.of_int (141))
                                                      (Prims.of_int (13))
                                                      (Prims.of_int (141))
                                                      (Prims.of_int (31)))
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Bind.fst"
                                                      (Prims.of_int (141))
                                                      (Prims.of_int (34))
                                                      (Prims.of_int (182))
                                                      (Prims.of_int (5)))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         Pulse_Syntax_Base.st_comp_of_comp
                                                           c1))
                                                   (fun uu___3 ->
                                                      (fun s1 ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Bind.fst"
                                                                 (Prims.of_int (142))
                                                                 (Prims.of_int (12))
                                                                 (Prims.of_int (142))
                                                                 (Prims.of_int (18)))
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Bind.fst"
                                                                 (Prims.of_int (142))
                                                                 (Prims.of_int (21))
                                                                 (Prims.of_int (182))
                                                                 (Prims.of_int (5)))
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___3
                                                                    ->
                                                                    s1.Pulse_Syntax_Base.res))
                                                              (fun uu___3 ->
                                                                 (fun t1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    g t1))
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
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_univ
                                                                    u
                                                                    s1.Pulse_Syntax_Base.u)
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
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (23)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (181))
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
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    s1.Pulse_Syntax_Base.post
                                                                    px))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    next_pre
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    (s1.Pulse_Syntax_Base.res))
                                                                    g))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    g'
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
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (99)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px)
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
                                                                    Pulse_Syntax_Base.uu___is_C_Tot
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
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Naming.close_st_term
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
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (181))
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
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (181))
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
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun s2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    g
                                                                    s2.Pulse_Syntax_Base.res))
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
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_univ
                                                                    u1
                                                                    s2.Pulse_Syntax_Base.u)
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
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    s2.Pulse_Syntax_Base.post)
                                                                    then
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (121)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (121)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (120)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    s2.Pulse_Syntax_Base.post))
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
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (27)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (85)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Typing.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun y ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (85)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    s2.Pulse_Syntax_Base.post
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    y)))
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
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (92)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (85)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    (Pulse_Typing.extend
                                                                    y
                                                                    (FStar_Pervasives.Inl
                                                                    (s2.Pulse_Syntax_Base.res))
                                                                    g)
                                                                    s2_post_opened))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    post_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (mk_bind
                                                                    g pre e11
                                                                    e2_closed
                                                                    c1 c2 px
                                                                    d1 () d22
                                                                    () ()))
                                                                    uu___10)))
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
                                                                    uu___5)))
                                                                    uu___5))))
                                                                    uu___3)))
                                                                   uu___3)))
                                                        uu___3)))) uu___1)))
                     uu___)
let (check_tot_bind :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
            Pulse_Checker_Common.check_t ->
              ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                 (unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun check ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                   (Prims.of_int (186)) (Prims.of_int (40))
                   (Prims.of_int (186)) (Prims.of_int (46)))
                (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                   (Prims.of_int (185)) (Prims.of_int (55))
                   (Prims.of_int (219)) (Prims.of_int (63)))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> t.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_TotBind
                          { Pulse_Syntax_Base.head2 = e1;
                            Pulse_Syntax_Base.body2 = e2;_}
                          ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                                  (Prims.of_int (187)) (Prims.of_int (48))
                                  (Prims.of_int (187)) (Prims.of_int (72)))
                               (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                                  (Prims.of_int (186)) (Prims.of_int (49))
                                  (Prims.of_int (219)) (Prims.of_int (63)))
                               (Obj.magic
                                  (Pulse_Checker_Pure.check_term_and_type g
                                     e1))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | FStar_Pervasives.Mkdtuple5
                                         (e11, u1, t1, _t1_typing, e1_typing)
                                         ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Bind.fst"
                                                 (Prims.of_int (188))
                                                 (Prims.of_int (10))
                                                 (Prims.of_int (191))
                                                 (Prims.of_int (21)))
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Bind.fst"
                                                 (Prims.of_int (191))
                                                 (Prims.of_int (24))
                                                 (Prims.of_int (219))
                                                 (Prims.of_int (63)))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    Pulse_Elaborate_Pure.tm_refine
                                                      {
                                                        Pulse_Syntax_Base.binder_ty
                                                          = t1;
                                                        Pulse_Syntax_Base.binder_ppname
                                                          =
                                                          FStar_Reflection_Typing.pp_name_default
                                                      }
                                                      (Pulse_Typing.mk_eq2 u1
                                                         t1
                                                         (Pulse_Elaborate_Pure.null_bvar
                                                            Prims.int_zero)
                                                         e11)))
                                              (fun uu___2 ->
                                                 (fun t11 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Bind.fst"
                                                            (Prims.of_int (193))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (193))
                                                            (Prims.of_int (41)))
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Bind.fst"
                                                            (Prims.of_int (191))
                                                            (Prims.of_int (24))
                                                            (Prims.of_int (219))
                                                            (Prims.of_int (63)))
                                                         (Obj.magic
                                                            (Pulse_Checker_Pure.check_term_with_expected_type
                                                               g e11 t11))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               match uu___2
                                                               with
                                                               | Prims.Mkdtuple2
                                                                   (e12,
                                                                    e1_typing1)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (17)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (20)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Base.v_as_nv
                                                                    x))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    t11) g))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (32)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (63)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    g' pre))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    pre_typing'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (63)))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px)
                                                                    pre ()
                                                                    post_hint))
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e21, c2,
                                                                    e2_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.uu___is_C_Tot
                                                                    c2
                                                                    then
                                                                    FStar_Tactics_Derived.fail
                                                                    "Tm_TotBind: e2 is not a stateful computation"
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_TotBind
                                                                    {
                                                                    Pulse_Syntax_Base.head2
                                                                    = e12;
                                                                    Pulse_Syntax_Base.body2
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    e21 x)
                                                                    })),
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c2 x) e12),
                                                                    (Pulse_Typing.T_TotBind
                                                                    (g, e12,
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    e21 x),
                                                                    t11, c2,
                                                                    x, (),
                                                                    e2_typing)))))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                              uu___2)))
                                                   uu___2))) uu___1))) uu___)