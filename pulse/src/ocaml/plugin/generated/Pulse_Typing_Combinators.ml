open Prims
let (st_comp_with_pre :
  Pulse_Syntax_Base.st_comp ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_comp)
  =
  fun st ->
    fun pre ->
      {
        Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
        Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
        Pulse_Syntax_Base.pre = pre;
        Pulse_Syntax_Base.post = (st.Pulse_Syntax_Base.post)
      }
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
  Pulse_Typing_Env.env ->
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
                             Pulse_Syntax_Base.comp_st,
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
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (40)) (Prims.of_int (13))
                                     (Prims.of_int (40)) (Prims.of_int (15)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Typing.Combinators.fst"
                                     (Prims.of_int (39)) (Prims.of_int (38))
                                     (Prims.of_int (121)) (Prims.of_int (82)))))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> px))
                            (fun uu___ ->
                               (fun uu___ ->
                                  match uu___ with
                                  | (uu___1, x) ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (41))
                                                    (Prims.of_int (10))
                                                    (Prims.of_int (41))
                                                    (Prims.of_int (41)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Combinators.fst"
                                                    (Prims.of_int (42))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (121))
                                                    (Prims.of_int (82)))))
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
                                                             Obj.repr
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
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
                                                                    ())))))))
                                                           else
                                                             Obj.repr
                                                               (Pulse_Typing_Env.fail
                                                                  g
                                                                  FStar_Pervasives_Native.None
                                                                  "Cannot compose two stghost computations with different opened invariants")))
                                                 | (Pulse_Syntax_Base.C_STAtomic
                                                    (inames, uu___2),
                                                    Pulse_Syntax_Base.C_ST
                                                    uu___3) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames
                                                               Pulse_Syntax_Base.tm_emp_inames
                                                           then
                                                             Obj.repr
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
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
                                                                    ())))))))
                                                           else
                                                             Obj.repr
                                                               (Pulse_Typing_Env.fail
                                                                  g
                                                                  FStar_Pervasives_Native.None
                                                                  "Cannot compose atomic with non-emp opened invariants with stt")))
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
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (69)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (63)))))
                                                               (Obj.magic
                                                                  (Pulse_Checker_Pure.get_non_informative_witness
                                                                    g
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c1)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)))
                                                               (fun w ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
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
                                                                    ())))))))
                                                           else
                                                             Pulse_Typing_Env.fail
                                                               g
                                                               FStar_Pervasives_Native.None
                                                               "Cannot compose ghost and atomic with different opened invariants"))
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
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (69)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (63)))))
                                                               (Obj.magic
                                                                  (Pulse_Checker_Pure.get_non_informative_witness
                                                                    g
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c2)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c2)))
                                                               (fun w ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
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
                                                                    ())))))))
                                                           else
                                                             Pulse_Typing_Env.fail
                                                               g
                                                               FStar_Pervasives_Native.None
                                                               "Cannot compose atomic and ghost with different opened invariants"))
                                                 | (Pulse_Syntax_Base.C_ST
                                                    uu___2,
                                                    Pulse_Syntax_Base.C_STAtomic
                                                    (inames, uu___3)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames
                                                               Pulse_Syntax_Base.tm_emp_inames
                                                           then
                                                             Obj.repr
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
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
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)),
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px),
                                                                    c2,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)),
                                                                    d_e2,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)), c2)))),
                                                                    (Pulse_Typing.Bind_comp
                                                                    (g, x,
                                                                    c1,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)), (),
                                                                    x, ())))))))
                                                           else
                                                             Obj.repr
                                                               (Pulse_Typing_Env.fail
                                                                  g
                                                                  FStar_Pervasives_Native.None
                                                                  "Cannot compose stt with atomic with non-emp opened invariants")))
                                                 | (Pulse_Syntax_Base.C_STGhost
                                                    (inames, uu___2),
                                                    Pulse_Syntax_Base.C_ST
                                                    uu___3) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames
                                                               Pulse_Syntax_Base.tm_emp_inames
                                                           then
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (69)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (81)))))
                                                               (Obj.magic
                                                                  (Pulse_Checker_Pure.get_non_informative_witness
                                                                    g
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c1)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)))
                                                               (fun uu___4 ->
                                                                  (fun w ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (81)))))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (81)))))
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
                                                                    uu___4)
                                                           else
                                                             Pulse_Typing_Env.fail
                                                               g
                                                               FStar_Pervasives_Native.None
                                                               "Cannot compose ghost with stt with non-emp opened invariants"))
                                                 | (Pulse_Syntax_Base.C_ST
                                                    uu___2,
                                                    Pulse_Syntax_Base.C_STGhost
                                                    (inames, uu___3)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames
                                                               Pulse_Syntax_Base.tm_emp_inames
                                                           then
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (54)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (19)))))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)))
                                                               (fun uu___4 ->
                                                                  (fun g' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (19)))))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (19)))))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.T_Lift
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    g
                                                                    (FStar_Pervasives_Native.snd
                                                                    px)
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)),
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (mk_bind
                                                                    g pre e1
                                                                    e2 c1
                                                                    c2lifted
                                                                    px d_e1
                                                                    () d_e21
                                                                    () ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)
                                                           else
                                                             Pulse_Typing_Env.fail
                                                               g
                                                               FStar_Pervasives_Native.None
                                                               "Cannot compose stt with ghost with non-emp opened invariants"))
                                                 | (Pulse_Syntax_Base.C_STAtomic
                                                    (inames, uu___2),
                                                    Pulse_Syntax_Base.C_STAtomic
                                                    (uu___3, uu___4)) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (if
                                                             Pulse_Syntax_Base.eq_tm
                                                               inames
                                                               Pulse_Syntax_Base.tm_emp_inames
                                                           then
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (46)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (81)))))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___5
                                                                    ->
                                                                    Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)))
                                                               (fun uu___5 ->
                                                                  (fun
                                                                    c1lifted
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (81)))))
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
                                                                    uu___5)
                                                           else
                                                             Pulse_Typing_Env.fail
                                                               g
                                                               FStar_Pervasives_Native.None
                                                               "Cannot compose statomics with non-emp opened invariants"))
                                                 | (uu___2, uu___3) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (Pulse_Typing_Env.fail
                                                             g
                                                             FStar_Pervasives_Native.None
                                                             "bind either not implemented (e.g. ghost) or not possible")))
                                                uu___2))) uu___)
let (bind_res_and_post_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_comp ->
      Pulse_Syntax_Base.var ->
        unit Pulse_Typing.post_hint_opt ->
          ((unit * unit), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun s2 ->
               fun x ->
                 fun post_hint ->
                   match post_hint with
                   | FStar_Pervasives_Native.None ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Combinators.fst"
                                        (Prims.of_int (133))
                                        (Prims.of_int (32))
                                        (Prims.of_int (133))
                                        (Prims.of_int (55)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Combinators.fst"
                                        (Prims.of_int (130))
                                        (Prims.of_int (13))
                                        (Prims.of_int (144))
                                        (Prims.of_int (7)))))
                               (Obj.magic
                                  (Pulse_Checker_Pure.check_universe g
                                     s2.Pulse_Syntax_Base.res))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     match uu___ with
                                     | Prims.Mkdtuple2 (u, res_typing) ->
                                         if
                                           Prims.op_Negation
                                             (Pulse_Syntax_Base.eq_univ u
                                                s2.Pulse_Syntax_Base.u)
                                         then
                                           Obj.magic
                                             (Pulse_Typing_Env.fail g
                                                FStar_Pervasives_Native.None
                                                "Unexpected universe for result type")
                                         else
                                           if
                                             FStar_Set.mem x
                                               (Pulse_Syntax_Naming.freevars
                                                  s2.Pulse_Syntax_Base.post)
                                           then
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (137))
                                                           (Prims.of_int (23))
                                                           (Prims.of_int (137))
                                                           (Prims.of_int (122)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (137))
                                                           (Prims.of_int (11))
                                                           (Prims.of_int (137))
                                                           (Prims.of_int (122)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Typing.Combinators.fst"
                                                                 (Prims.of_int (137))
                                                                 (Prims.of_int (95))
                                                                 (Prims.of_int (137))
                                                                 (Prims.of_int (121)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "prims.fst"
                                                                 (Prims.of_int (590))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (590))
                                                                 (Prims.of_int (31)))))
                                                        (Obj.magic
                                                           (Pulse_Syntax_Printer.term_to_string
                                                              s2.Pulse_Syntax_Base.post))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                Prims.strcat
                                                                  (Prims.strcat
                                                                    "Bound variable "
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    x)
                                                                    " escapes scope in postcondition "))
                                                                  (Prims.strcat
                                                                    uu___2 "")))))
                                                  (fun uu___2 ->
                                                     (fun uu___2 ->
                                                        Obj.magic
                                                          (Pulse_Typing_Env.fail
                                                             g
                                                             FStar_Pervasives_Native.None
                                                             uu___2)) uu___2))
                                           else
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (139))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (139))
                                                           (Prims.of_int (17)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Typing.Combinators.fst"
                                                           (Prims.of_int (139))
                                                           (Prims.of_int (20))
                                                           (Prims.of_int (143))
                                                           (Prims.of_int (31)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 -> x))
                                                  (fun uu___3 ->
                                                     (fun y ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (61)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (31)))))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   Pulse_Syntax_Naming.open_term_nv
                                                                    s2.Pulse_Syntax_Base.post
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    y)))
                                                             (fun uu___3 ->
                                                                (fun
                                                                   s2_post_opened
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Typing.Combinators.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g y
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    s2.Pulse_Syntax_Base.res)
                                                                    s2_post_opened))
                                                                    (fun
                                                                    post_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ((), ())))))
                                                                  uu___3)))
                                                       uu___3))) uu___)))
                   | FStar_Pervasives_Native.Some post ->
                       Obj.magic
                         (Obj.repr
                            (if
                               FStar_Set.mem x
                                 (Pulse_Syntax_Naming.freevars
                                    s2.Pulse_Syntax_Base.post)
                             then
                               Obj.repr
                                 (Pulse_Typing_Env.fail g
                                    FStar_Pervasives_Native.None
                                    "Unexpected mismatched postcondition in bind")
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 -> ((), ())))))) uu___3
            uu___2 uu___1 uu___
let (add_frame :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              (Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
                (unit, unit, unit) Pulse_Typing.st_typing)
                FStar_Pervasives.dtuple3)
  =
  fun g ->
    fun t ->
      fun c ->
        fun t_typing ->
          fun frame ->
            fun frame_typing ->
              FStar_Pervasives.Mkdtuple3
                (t, (Pulse_Typing.add_frame c frame),
                  (Pulse_Typing.T_Frame (g, t, c, frame, (), t_typing)))