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
              let uu___ =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> t)) in
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
                         (Prims.of_int (96)) (Prims.of_int (55)))))
                (Obj.magic uu___)
                (fun uu___1 ->
                   (fun t0 ->
                      let uu___1 =
                        Obj.magic
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 ->
                                Pulse_Typing_Env.push_context g "check_admit"
                                  t.Pulse_Syntax_Base.range1)) in
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
                                    (Prims.of_int (96)) (Prims.of_int (55)))))
                           (Obj.magic uu___1)
                           (fun uu___2 ->
                              (fun g1 ->
                                 let uu___2 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___3 ->
                                           t.Pulse_Syntax_Base.term1)) in
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
                                               (Prims.of_int (96))
                                               (Prims.of_int (55)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         (fun uu___3 ->
                                            match uu___3 with
                                            | Pulse_Syntax_Base.Tm_Admit
                                                { Pulse_Syntax_Base.ctag = c;
                                                  Pulse_Syntax_Base.u1 =
                                                    uu___4;
                                                  Pulse_Syntax_Base.typ = t1;
                                                  Pulse_Syntax_Base.post3 =
                                                    post;_}
                                                ->
                                                let uu___5 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___6 ->
                                                          Pulse_Typing_Env.fresh
                                                            g1)) in
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
                                                              (Prims.of_int (96))
                                                              (Prims.of_int (55)))))
                                                     (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        (fun x ->
                                                           let uu___6 =
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___7
                                                                    ->
                                                                    Pulse_Syntax_Base.v_as_nv
                                                                    x)) in
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
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (55)))))
                                                                (Obj.magic
                                                                   uu___6)
                                                                (fun uu___7
                                                                   ->
                                                                   (fun px ->
                                                                    let uu___7
                                                                    =
                                                                    match 
                                                                    (post,
                                                                    post_hint)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "could not find a post annotation on admit, please add one"
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    post1,
                                                                    FStar_Pervasives_Native.Some
                                                                    post2) ->
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    post2.Pulse_Typing.post in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    post1 in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "found two post annotations on admit: "
                                                                    (Prims.strcat
                                                                    uu___13
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    ", please remove one"))) in
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
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    uu___12
                                                                    uu___10))))
                                                                    uu___10) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___9))
                                                                    uu___9)
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    post1,
                                                                    uu___8)
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Pulse_Checker_Pure.check_universe
                                                                    g1 t1 in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u,
                                                                    t_typing)
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post1 px)) in
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
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    post_opened
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Pulse_Checker_Pure.check_tot_term
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px) t1)
                                                                    post_opened
                                                                    Pulse_Syntax_Pure.tm_slprop in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___13
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
                                                                    uu___12)))
                                                                    uu___10)
                                                                    | 
                                                                    (uu___8,
                                                                    FStar_Pervasives_Native.Some
                                                                    post1) ->
                                                                    Pulse_Typing_Combinators.comp_for_post_hint
                                                                    g pre ()
                                                                    post1 x in
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
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun res
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    res)) in
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
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c1, d_c)
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing.T_Admit
                                                                    (g1, c1,
                                                                    d_c))) in
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
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun d ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_BreakVC.break_vc
                                                                    ()) in
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
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.ide
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun ide
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.ext_getv
                                                                    "pulse:no_admit_diag" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    uu___16 =
                                                                    "1")) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    no_admit_diag
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    if
                                                                    ide &&
                                                                    (Prims.op_Negation
                                                                    no_admit_diag)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___16
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.norm_well_typed_term
                                                                    (Pulse_Typing.elab_env
                                                                    g1)
                                                                    [FStar_Pervasives.unascribe;
                                                                    FStar_Pervasives.primops;
                                                                    FStar_Pervasives.iota]
                                                                    pre in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun pre1
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    Pulse_Syntax_Pure.canon_slprop_print
                                                                    pre1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    uu___23))
                                                                    uu___23) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Pulse_PP.indent
                                                                    uu___22)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "Current context:")
                                                                    uu___21)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    [uu___20])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (Pulse_PP.text
                                                                    "Admitting continuation.")
                                                                    ::
                                                                    uu___19)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun msg
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.info_doc_env
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t0.Pulse_Syntax_Base.range1))
                                                                    msg))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
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
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                          uu___6))) uu___3)))
                                uu___2))) uu___1)