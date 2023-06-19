open Prims
let (check_stapp :
  Prims.bool ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Checker_Common.post_hint_opt ->
              (Prims.bool -> Pulse_Checker_Common.check_t) ->
                ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun check' ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                           (Prims.of_int (25)) (Prims.of_int (14))
                           (Prims.of_int (25)) (Prims.of_int (21)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.STApp.fst"
                           (Prims.of_int (25)) (Prims.of_int (24))
                           (Prims.of_int (91)) (Prims.of_int (117)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> t.Pulse_Syntax_Base.range1))
                  (fun uu___ ->
                     (fun range ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.STApp.fst"
                                      (Prims.of_int (26)) (Prims.of_int (46))
                                      (Prims.of_int (26)) (Prims.of_int (52)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.STApp.fst"
                                      (Prims.of_int (25)) (Prims.of_int (24))
                                      (Prims.of_int (91))
                                      (Prims.of_int (117)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> t.Pulse_Syntax_Base.term1))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | Pulse_Syntax_Base.Tm_STApp
                                       { Pulse_Syntax_Base.head = head;
                                         Pulse_Syntax_Base.arg_qual = qual;
                                         Pulse_Syntax_Base.arg = arg;_}
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.STApp.fst"
                                                     (Prims.of_int (35))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (47))
                                                     (Prims.of_int (64)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.STApp.fst"
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (91))
                                                     (Prims.of_int (117)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  fun uu___2 ->
                                                    fun uu___1 ->
                                                      (fun uu___1 ->
                                                         fun t1 ->
                                                           fun c ->
                                                             match c with
                                                             | Pulse_Syntax_Base.C_Tot
                                                                 ty ->
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (match 
                                                                    Pulse_Syntax_Pure.is_arrow
                                                                    ty
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (uu___2,
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.Implicit),
                                                                    uu___3)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.infer
                                                                    g t1 ty
                                                                    pre range))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (check'
                                                                    false g
                                                                    t2 pre ()
                                                                    post_hint))
                                                                    uu___4))
                                                                    | 
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Unexpected c in infer_logical_implicits_and_check")))
                                                             | uu___2 ->
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Unexpected c in infer_logical_implicits_and_check")))
                                                        uu___3 uu___2 uu___1))
                                            (fun uu___1 ->
                                               (fun
                                                  infer_logical_implicits_and_check
                                                  ->
                                                  Obj.magic
                                                    (FStar_Tactics_V2_Derived.or_else
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (47)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (52)))))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  Pulse_Checker_Pure.push_context
                                                                    "pure_app"
                                                                    t.Pulse_Syntax_Base.range1
                                                                    g))
                                                            (fun uu___2 ->
                                                               (fun g1 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Pure.tm_pureapp
                                                                    head qual
                                                                    arg))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    pure_app
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.instantiate_term_implicits
                                                                    g1
                                                                    pure_app))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (t1, ty)
                                                                    ->
                                                                    Obj.magic
                                                                    (infer_logical_implicits_and_check
                                                                    t1
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    ty)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                 uu___2))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (45)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (116)))))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  Pulse_Checker_Pure.push_context
                                                                    "st_app"
                                                                    t.Pulse_Syntax_Base.range1
                                                                    g))
                                                            (fun uu___2 ->
                                                               (fun g1 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (116)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term
                                                                    g1 head))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (head1,
                                                                    ty_head,
                                                                    dhead) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (116)))))
                                                                    (if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g1)
                                                                    "st_app"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty_head))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "st_app: head = "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    ", ty_head = "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___3))
                                                                    uu___3)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match 
                                                                    Pulse_Syntax_Pure.is_arrow
                                                                    ty_head
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ({
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = formal;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;_},
                                                                    bqual,
                                                                    comp_typ)
                                                                    ->
                                                                    if
                                                                    qual =
                                                                    bqual
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g1 arg
                                                                    formal))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (arg1,
                                                                    darg) ->
                                                                    (match comp_typ
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_ST
                                                                    res ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g1,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.repack
                                                                    g pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    uu___5
                                                                    post_hint))
                                                                    uu___5)))
                                                                    uu___5))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___5,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g1,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.repack
                                                                    g pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    uu___6
                                                                    post_hint))
                                                                    uu___6)))
                                                                    uu___6))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (uu___5,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g1,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1) d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.repack
                                                                    g pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    = head1;
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    = qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    }))
                                                                    uu___6
                                                                    post_hint))
                                                                    uu___6)))
                                                                    uu___6))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Pure.tm_pureapp
                                                                    head1
                                                                    qual arg1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.open_comp_with
                                                                    comp_typ
                                                                    arg1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    comp_typ1
                                                                    ->
                                                                    Obj.magic
                                                                    (infer_logical_implicits_and_check
                                                                    t1
                                                                    comp_typ1))
                                                                    uu___6)))
                                                                    uu___6))))
                                                                    uu___4))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    arg))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty_head))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.range_to_string
                                                                    t.Pulse_Syntax_Base.range1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "("
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    ") Unexpected qualifier in head type "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " of stateful application: head = "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    ", arg = "))
                                                                    (Prims.strcat
                                                                    x2 "")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8
                                                                    uu___7))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    uu___6))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6
                                                                    uu___5))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___5))
                                                                    uu___5))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (116)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (116)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (115)))))
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
                                                                    ty_head))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Unexpected head type in impure application: "
                                                                    (Prims.strcat
                                                                    uu___5 "")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___5))
                                                                    uu___5)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                 uu___2))))
                                                 uu___1))) uu___))) uu___)