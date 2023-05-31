open Prims
let (check_return :
  Prims.bool ->
    Pulse_Typing.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Checker_Common.post_hint_opt ->
              ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun st ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                   (Prims.of_int (22)) (Prims.of_int (10))
                   (Prims.of_int (22)) (Prims.of_int (39)))
                (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                   (Prims.of_int (22)) (Prims.of_int (42))
                   (Prims.of_int (49)) (Prims.of_int (68)))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Checker_Pure.push_context "check_return" g))
                (fun uu___ ->
                   (fun g1 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                              (Prims.of_int (23)) (Prims.of_int (53))
                              (Prims.of_int (23)) (Prims.of_int (60)))
                           (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                              (Prims.of_int (22)) (Prims.of_int (42))
                              (Prims.of_int (49)) (Prims.of_int (68)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> st.Pulse_Syntax_Base.term1))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | Pulse_Syntax_Base.Tm_Return
                                     { Pulse_Syntax_Base.ctag = c;
                                       Pulse_Syntax_Base.insert_eq = use_eq;
                                       Pulse_Syntax_Base.term = t;_}
                                     ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Return.fst"
                                             (Prims.of_int (24))
                                             (Prims.of_int (31))
                                             (Prims.of_int (24))
                                             (Prims.of_int (54)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Return.fst"
                                             (Prims.of_int (23))
                                             (Prims.of_int (63))
                                             (Prims.of_int (49))
                                             (Prims.of_int (68)))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.check_term_and_type
                                                g1 t))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple5
                                                    (t1, u, ty, uty, d) ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Return.fst"
                                                            (Prims.of_int (25))
                                                            (Prims.of_int (10))
                                                            (Prims.of_int (25))
                                                            (Prims.of_int (17)))
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Return.fst"
                                                            (Prims.of_int (25))
                                                            (Prims.of_int (20))
                                                            (Prims.of_int (49))
                                                            (Prims.of_int (68)))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               Pulse_Typing.fresh
                                                                 g1))
                                                         (fun uu___2 ->
                                                            (fun x ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (20)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (68)))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.v_as_nv
                                                                    x))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (68)))
                                                                    (match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (93)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    (Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    ty) g1)
                                                                    Pulse_Syntax_Base.Tm_Emp
                                                                    Pulse_Syntax_Base.Tm_VProp))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (t2, ty1)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (t2, ()))))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    post))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    post1 ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    post1.Pulse_Checker_Common.ret_ty
                                                                    ty)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (58)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (58)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (58)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (58)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    post1.Pulse_Checker_Common.ret_ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (58)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.range_to_string
                                                                    st.Pulse_Syntax_Base.range))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "("
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    ") Expected return type "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    ", got "))
                                                                    (Prims.strcat
                                                                    x2 "\n")))))
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
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___2)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    post1.Pulse_Checker_Common.post)
                                                                    then
                                                                    FStar_Tactics_Derived.fail
                                                                    "Unexpected variable clash in return"
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Naming.open_term_nv
                                                                    post1.Pulse_Checker_Common.post
                                                                    px), ())))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post_opened,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.T_Return
                                                                    (g1, c,
                                                                    use_eq,
                                                                    u, ty,
                                                                    t1, post,
                                                                    x, (),
                                                                    (), ())))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (68)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Return
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    = c;
                                                                    Pulse_Syntax_Base.insert_eq
                                                                    = use_eq;
                                                                    Pulse_Syntax_Base.term
                                                                    = t1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_return
                                                                    c use_eq
                                                                    u ty t1
                                                                    post x)
                                                                    d1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.repack
                                                                    g pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Return
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    = c;
                                                                    Pulse_Syntax_Base.insert_eq
                                                                    = use_eq;
                                                                    Pulse_Syntax_Base.term
                                                                    = t1
                                                                    }))
                                                                    uu___4
                                                                    post_hint))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                              uu___2)))
                                               uu___1))) uu___))) uu___)