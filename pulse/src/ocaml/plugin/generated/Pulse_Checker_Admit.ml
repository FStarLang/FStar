open Prims
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Admit.fst"
                         (Prims.of_int (39)) (Prims.of_int (21))
                         (Prims.of_int (39)) (Prims.of_int (22)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Admit.fst"
                         (Prims.of_int (39)) (Prims.of_int (25))
                         (Prims.of_int (93)) (Prims.of_int (55)))))
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t))
                (fun uu___ ->
                   (fun t0 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Admit.fst"
                                    (Prims.of_int (40)) (Prims.of_int (10))
                                    (Prims.of_int (40)) (Prims.of_int (63)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Admit.fst"
                                    (Prims.of_int (40)) (Prims.of_int (66))
                                    (Prims.of_int (93)) (Prims.of_int (55)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ ->
                                 Pulse_Typing_Env.push_context g
                                   "check_admit" t.Pulse_Syntax_Base.range1))
                           (fun uu___ ->
                              (fun g1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Admit.fst"
                                               (Prims.of_int (42))
                                               (Prims.of_int (43))
                                               (Prims.of_int (42))
                                               (Prims.of_int (49)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Admit.fst"
                                               (Prims.of_int (40))
                                               (Prims.of_int (66))
                                               (Prims.of_int (93))
                                               (Prims.of_int (55)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___ ->
                                            t.Pulse_Syntax_Base.term1))
                                      (fun uu___ ->
                                         (fun uu___ ->
                                            match uu___ with
                                            | Pulse_Syntax_Base.Tm_Admit
                                                { Pulse_Syntax_Base.ctag = c;
                                                  Pulse_Syntax_Base.u1 =
                                                    uu___1;
                                                  Pulse_Syntax_Base.typ = t1;
                                                  Pulse_Syntax_Base.post3 =
                                                    post;_}
                                                ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Admit.fst"
                                                              (Prims.of_int (44))
                                                              (Prims.of_int (10))
                                                              (Prims.of_int (44))
                                                              (Prims.of_int (17)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Admit.fst"
                                                              (Prims.of_int (44))
                                                              (Prims.of_int (20))
                                                              (Prims.of_int (93))
                                                              (Prims.of_int (55)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Pulse_Typing_Env.fresh
                                                             g1))
                                                     (fun uu___2 ->
                                                        (fun x ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (20)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (55)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.v_as_nv
                                                                    x))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun px ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (55)))))
                                                                    (match 
                                                                    (post,
                                                                    post_hint)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "could not find a post annotation on admit, please add one")
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    post1,
                                                                    FStar_Pervasives_Native.Some
                                                                    post2) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    post2.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    post1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "found two post annotations on admit: "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    ", please remove one")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___2))
                                                                    uu___2))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    post1,
                                                                    uu___2)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    g1 t1))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post1 px))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_tot_term
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px) t1)
                                                                    post_opened
                                                                    Pulse_Syntax_Pure.tm_vprop))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened1,
                                                                    post_typing)
                                                                    ->
                                                                    (match c
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.STT
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_ST
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }),
                                                                    (Pulse_Typing.CT_ST
                                                                    (g1,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    },
                                                                    (Pulse_Typing.STC
                                                                    (g1,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }, x, (),
                                                                    (), ())))))
                                                                    | 
                                                                    Pulse_Syntax_Base.STT_Ghost
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STGhost
                                                                    (Pulse_Syntax_Pure.tm_emp_inames,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    })),
                                                                    (Pulse_Typing.CT_STGhost
                                                                    (g1,
                                                                    Pulse_Syntax_Pure.tm_emp_inames,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }, (),
                                                                    (Pulse_Typing.STC
                                                                    (g1,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }, x, (),
                                                                    (), ())))))
                                                                    | 
                                                                    Pulse_Syntax_Base.STT_Atomic
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STAtomic
                                                                    (Pulse_Syntax_Pure.tm_emp_inames,
                                                                    Pulse_Syntax_Base.Neutral,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    })),
                                                                    (Pulse_Typing.CT_STAtomic
                                                                    (g1,
                                                                    Pulse_Syntax_Pure.tm_emp_inames,
                                                                    Pulse_Syntax_Base.Neutral,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }, (),
                                                                    (Pulse_Typing.STC
                                                                    (g1,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened1
                                                                    x)
                                                                    }, x, (),
                                                                    (), ()))))))))))
                                                                    uu___4)))
                                                                    uu___3))
                                                                    | 
                                                                    (uu___2,
                                                                    FStar_Pervasives_Native.Some
                                                                    post1) ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Combinators.comp_for_post_hint
                                                                    g pre ()
                                                                    post1 x))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun res
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    res))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c1, d_c)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Admit
                                                                    (g1, c1,
                                                                    d_c)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_BreakVC.break_vc
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.ide
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    if uu___4
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Pure.canon_vprop_print
                                                                    pre))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_PP.indent
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "Current context:")
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    [uu___5]))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (Pulse_PP.text
                                                                    "Admitting continuation.")
                                                                    :: uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun msg
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.info_doc_env
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t0.Pulse_Syntax_Base.range1))
                                                                    msg))
                                                                    uu___5)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    ()))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c1))
                                                                    (Pulse_Syntax_Base.Tm_Admit
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    =
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c1);
                                                                    Pulse_Syntax_Base.u1
                                                                    =
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c1);
                                                                    Pulse_Syntax_Base.typ
                                                                    =
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1);
                                                                    Pulse_Syntax_Base.post3
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })), c1,
                                                                    d))
                                                                    res_ppname))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                          uu___2))) uu___)))
                                uu___))) uu___)