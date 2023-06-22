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
                           (Prims.of_int (94)) (Prims.of_int (19)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> t.Pulse_Syntax_Base.range2))
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
                                      (Prims.of_int (94)) (Prims.of_int (19)))))
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
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (67))
                                                     (Prims.of_int (82))
                                                     (Prims.of_int (126)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.STApp.fst"
                                                     (Prims.of_int (83))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (94))
                                                     (Prims.of_int (19)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  fun uu___2 ->
                                                    FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.STApp.fst"
                                                               (Prims.of_int (50))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (50))
                                                               (Prims.of_int (43)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.STApp.fst"
                                                               (Prims.of_int (50))
                                                               (Prims.of_int (46))
                                                               (Prims.of_int (82))
                                                               (Prims.of_int (126)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            Pulse_Checker_Pure.push_context
                                                              "st_app"
                                                              t.Pulse_Syntax_Base.range2
                                                              g))
                                                      (fun uu___3 ->
                                                         (fun g1 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (54)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (126)))))
                                                                 (Obj.magic
                                                                    (
                                                                    Pulse_Checker_Pure.check_term
                                                                    g1 head))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
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
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (126)))))
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
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty_head))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (54))
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
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "st_app: head = "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    ", ty_head = "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    uu___4))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___4))
                                                                    uu___4)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
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
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (129)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g1 arg
                                                                    formal))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
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
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (73))
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
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (73))
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
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___6,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g1,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (73))
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
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
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
                                                                    uu___7
                                                                    post_hint))
                                                                    uu___7)))
                                                                    uu___7))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (uu___6,
                                                                    res) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing.T_STApp
                                                                    (g1,
                                                                    head1,
                                                                    formal,
                                                                    qual,
                                                                    comp_typ,
                                                                    arg1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (73))
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
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
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
                                                                    uu___7
                                                                    post_hint))
                                                                    uu___7)))
                                                                    uu___7))
                                                                    | 
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    "Expected an effectful application; got a pure term (could it be partially applied by mistake?)")))
                                                                    uu___5))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    arg))
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
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    head1))
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
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (60)))))
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
                                                                    ty_head))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Unexpected qualifier in head type "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    " of stateful application: head = "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", arg = "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
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
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    uu___6))
                                                                    uu___6))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (126)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (126)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (125)))))
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
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "Unexpected head type in impure application: "
                                                                    (Prims.strcat
                                                                    uu___6 "")))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    uu___6))
                                                                    uu___6)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                           uu___3)))
                                            (fun uu___1 ->
                                               (fun check_st_app ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.STApp.fst"
                                                                (Prims.of_int (85))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (85))
                                                                (Prims.of_int (43)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.STApp.fst"
                                                                (Prims.of_int (85))
                                                                (Prims.of_int (46))
                                                                (Prims.of_int (94))
                                                                (Prims.of_int (19)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___1 ->
                                                             Pulse_Checker_Pure.push_context
                                                               "pure_app"
                                                               t.Pulse_Syntax_Base.range2
                                                               g))
                                                       (fun uu___1 ->
                                                          (fun g1 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (41)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (19)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Pure.tm_pureapp
                                                                    head qual
                                                                    arg))
                                                                  (fun uu___1
                                                                    ->
                                                                    (fun
                                                                    pure_app
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.instantiate_term_implicits
                                                                    g1
                                                                    pure_app))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    (t1, ty)
                                                                    ->
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.STApp.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.infer
                                                                    g1 t1 ty
                                                                    pre range))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (check'
                                                                    false g1
                                                                    t2 pre ()
                                                                    post_hint))
                                                                    uu___4))
                                                                    | 
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (check_st_app
                                                                    ())))
                                                                    uu___1)))
                                                                    uu___1)))
                                                            uu___1))) uu___1)))
                                  uu___))) uu___)