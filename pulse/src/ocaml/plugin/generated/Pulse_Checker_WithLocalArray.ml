open Prims
let (extend_post_hint :
  Pulse_Typing_Env.env ->
    unit Pulse_Typing.post_hint_for_env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.var -> unit Pulse_Typing.post_hint_for_env)
  =
  fun g ->
    fun p ->
      fun init_t ->
        fun x ->
          {
            Pulse_Typing.g = (p.Pulse_Typing.g);
            Pulse_Typing.ctag_hint = (p.Pulse_Typing.ctag_hint);
            Pulse_Typing.ret_ty = (p.Pulse_Typing.ret_ty);
            Pulse_Typing.u = (p.Pulse_Typing.u);
            Pulse_Typing.ty_typing = ();
            Pulse_Typing.post =
              (Pulse_Typing.comp_withlocal_array_body_post
                 p.Pulse_Typing.post init_t (Pulse_Syntax_Pure.null_var x));
            Pulse_Typing.post_typing = ()
          }

let (is_annotated_type_array :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match Pulse_Syntax_Pure.is_pure_app t with
    | FStar_Pervasives_Native.Some (head, FStar_Pervasives_Native.None, a) ->
        (match Pulse_Syntax_Pure.is_fvar head with
         | FStar_Pervasives_Native.Some (l, uu___) ->
             if l = Pulse_Reflection_Util.array_lid
             then FStar_Pervasives_Native.Some a
             else FStar_Pervasives_Native.None
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Checker_Base.check_t ->
                ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              fun check1 ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.WithLocalArray.fst"
                           (Prims.of_int (58)) (Prims.of_int (10))
                           (Prims.of_int (58)) (Prims.of_int (56)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.WithLocalArray.fst"
                           (Prims.of_int (58)) (Prims.of_int (59))
                           (Prims.of_int (139)) (Prims.of_int (38)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Checker_Pure.push_context
                          "check_withlocal_array" t.Pulse_Syntax_Base.range2
                          g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.WithLocalArray.fst"
                                      (Prims.of_int (59)) (Prims.of_int (62))
                                      (Prims.of_int (59)) (Prims.of_int (68)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.WithLocalArray.fst"
                                      (Prims.of_int (58)) (Prims.of_int (59))
                                      (Prims.of_int (139))
                                      (Prims.of_int (38)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> t.Pulse_Syntax_Base.term1))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | Pulse_Syntax_Base.Tm_WithLocalArray
                                       { Pulse_Syntax_Base.binder3 = binder;
                                         Pulse_Syntax_Base.initializer2 =
                                           initializer1;
                                         Pulse_Syntax_Base.length = length;
                                         Pulse_Syntax_Base.body5 = body;_}
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.WithLocalArray.fst"
                                                     (Prims.of_int (60))
                                                     (Prims.of_int (62))
                                                     (Prims.of_int (78))
                                                     (Prims.of_int (83)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.WithLocalArray.fst"
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (71))
                                                     (Prims.of_int (139))
                                                     (Prims.of_int (38)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.WithLocalArray.fst"
                                                           (Prims.of_int (62))
                                                           (Prims.of_int (13))
                                                           (Prims.of_int (62))
                                                           (Prims.of_int (29)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.WithLocalArray.fst"
                                                           (Prims.of_int (63))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (78))
                                                           (Prims.of_int (83)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 ->
                                                        binder.Pulse_Syntax_Base.binder_ty))
                                                  (fun uu___1 ->
                                                     (fun ty ->
                                                        match ty.Pulse_Syntax_Base.t
                                                        with
                                                        | Pulse_Syntax_Base.Tm_Unknown
                                                            ->
                                                            Obj.magic
                                                              (Pulse_Checker_Pure.check_tot_term_and_type
                                                                 g1
                                                                 initializer1)
                                                        | uu___1 ->
                                                            (match is_annotated_type_array
                                                                    ty
                                                             with
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (34)))))
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
                                                                    ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "expected annotated type to be an array, found: "
                                                                    (Prims.strcat
                                                                    uu___2 "")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (ty.Pulse_Syntax_Base.range1))
                                                                    uu___2))
                                                                    uu___2))
                                                             | FStar_Pervasives_Native.Some
                                                                 ty1 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (83)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    g1 ty1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u,
                                                                    ty_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (83)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type_and_effect
                                                                    g1
                                                                    initializer1
                                                                    FStar_TypeChecker_Core.E_Total
                                                                    ty1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (init,
                                                                    init_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (init, u,
                                                                    ty1, (),
                                                                    ())))))
                                                                    uu___2))))
                                                       uu___1)))
                                            (fun uu___1 ->
                                               (fun uu___1 ->
                                                  match uu___1 with
                                                  | FStar_Pervasives.Mkdtuple5
                                                      (init, init_u, init_t,
                                                       init_t_typing,
                                                       init_typing)
                                                      ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (53)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (38)))))
                                                           (Obj.magic
                                                              (Pulse_Checker_Pure.check_tot_term_with_expected_type
                                                                 g1 length
                                                                 Pulse_Typing.tm_nat))
                                                           (fun uu___2 ->
                                                              (fun uu___2 ->
                                                                 match uu___2
                                                                 with
                                                                 | Prims.Mkdtuple2
                                                                    (len,
                                                                    len_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_univ
                                                                    init_u
                                                                    Pulse_Syntax_Pure.u0
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ((binder.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun px
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars_st
                                                                    body)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Unseal.unseal
                                                                    (binder.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "withlocalarray: "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " is free in body")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range2))
                                                                    uu___3))
                                                                    uu___3))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Pure.term_of_nvar
                                                                    px))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun x_tm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    binder.Pulse_Syntax_Base.binder_ppname
                                                                    (Pulse_Typing.mk_array
                                                                    init_t)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    g_extended
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.comp_withlocal_array_body_pre
                                                                    pre
                                                                    init_t
                                                                    x_tm init
                                                                    len))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body_pre
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body_pre_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (match post_hint
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    post)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Allocating a mutable local array expects an annotated post-condition")))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun post
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    post.Pulse_Typing.post)
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Impossible! check_withlocal: unexpected name clash in with_local,please file a bug-report")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    extend_post_hint
                                                                    g1 post
                                                                    init_t x))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    body_post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (117)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (check1
                                                                    g_extended
                                                                    body_pre
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    body_post)
                                                                    binder.Pulse_Syntax_Base.binder_ppname
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body px)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g_extended
                                                                    body_pre
                                                                    body_post
                                                                    r
                                                                    binder.Pulse_Syntax_Base.binder_ppname))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (opened_body,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.uu___is_C_ST
                                                                    c_body)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c_body))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "check_withlocalarray: body computation type "
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    " is not ST")))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range2))
                                                                    uu___6))
                                                                    uu___6))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    opened_body
                                                                    x))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Base.C_ST
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c_body);
                                                                    Pulse_Syntax_Base.res
                                                                    =
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c_body);
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (post.Pulse_Typing.post)
                                                                    }))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun c ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (100)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (100)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing.post_hint_typing
                                                                    g1 post x))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    post_typing_rec
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.intro_comp_typing
                                                                    g1 c ()
                                                                    () x ()))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing.T_WithLocalArray
                                                                    (g1,
                                                                    init,
                                                                    len,
                                                                    body1,
                                                                    init_t,
                                                                    c, x, (),
                                                                    (), (),
                                                                    c_typing,
                                                                    body_typing)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    c
                                                                    (Pulse_Syntax_Base.Tm_WithLocalArray
                                                                    {
                                                                    Pulse_Syntax_Base.binder3
                                                                    =
                                                                    (Pulse_Typing.as_binder
                                                                    (Pulse_Typing.mk_array
                                                                    init_t));
                                                                    Pulse_Syntax_Base.initializer2
                                                                    = init;
                                                                    Pulse_Syntax_Base.length
                                                                    = len;
                                                                    Pulse_Syntax_Base.body5
                                                                    = body1
                                                                    })), c,
                                                                    d))
                                                                    res_ppname))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocalArray.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (35)))))
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
                                                                    init))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_withlocalarray: allocating a local variable: type "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " is not universe zero (computed "))
                                                                    (Prims.strcat
                                                                    x ")")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    (Pulse_Syntax_Printer.univ_to_string
                                                                    init_u)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    uu___4))
                                                                    uu___4)))
                                                                uu___2)))
                                                 uu___1))) uu___))) uu___)