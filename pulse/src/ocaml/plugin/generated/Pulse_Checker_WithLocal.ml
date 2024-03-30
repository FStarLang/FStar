open Prims
let (extend_post_hint_for_local :
  Pulse_Typing_Env.env ->
    unit Pulse_Typing.post_hint_for_env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.var ->
          (unit Pulse_Typing.post_hint_for_env, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      fun init_t ->
        fun x ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.WithLocal.fst"
                     (Prims.of_int (36)) (Prims.of_int (19))
                     (Prims.of_int (36)) (Prims.of_int (99)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.WithLocal.fst"
                     (Prims.of_int (36)) (Prims.of_int (102))
                     (Prims.of_int (40)) (Prims.of_int (7)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  Pulse_Syntax_Pure.tm_exists_sl Pulse_Syntax_Pure.u0
                    (Pulse_Syntax_Base.as_binder init_t)
                    (Pulse_Typing.mk_pts_to init_t
                       (Pulse_Syntax_Pure.null_var x)
                       (Pulse_Syntax_Pure.null_bvar Prims.int_zero))))
            (fun uu___ ->
               (fun conjunct ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.WithLocal.fst"
                                (Prims.of_int (37)) (Prims.of_int (13))
                                (Prims.of_int (37)) (Prims.of_int (60)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.WithLocal.fst"
                                (Prims.of_int (37)) (Prims.of_int (63))
                                (Prims.of_int (40)) (Prims.of_int (7)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             Pulse_Typing_Env.push_binding g x
                               Pulse_Syntax_Base.ppname_default
                               (Pulse_Typing.mk_ref init_t)))
                       (fun uu___ ->
                          (fun g' ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.WithLocal.fst"
                                           (Prims.of_int (38))
                                           (Prims.of_int (19))
                                           (Prims.of_int (38))
                                           (Prims.of_int (84)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.WithLocal.fst"
                                           (Prims.of_int (38))
                                           (Prims.of_int (87))
                                           (Prims.of_int (40))
                                           (Prims.of_int (7)))))
                                  (Obj.magic
                                     (Pulse_Checker_Pure.core_check_term g'
                                        conjunct
                                        FStar_TypeChecker_Core.E_Total
                                        Pulse_Syntax_Pure.tm_vprop))
                                  (fun uu___ ->
                                     (fun c_typing ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.WithLocal.fst"
                                                      (Prims.of_int (39))
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (39))
                                                      (Prims.of_int (82)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.WithLocal.fst"
                                                      (Prims.of_int (39))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (39))
                                                      (Prims.of_int (11)))))
                                             (Obj.magic
                                                (Pulse_Checker_Base.extend_post_hint
                                                   g p x
                                                   (Pulse_Typing.mk_ref
                                                      init_t) conjunct ()))
                                             (fun res ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___ -> res)))) uu___)))
                            uu___))) uu___)

let (head_range : Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.range) =
  fun t ->
    let uu___ = t.Pulse_Syntax_Base.term1 in
    match uu___ with
    | Pulse_Syntax_Base.Tm_WithLocal
        { Pulse_Syntax_Base.binder2 = uu___1;
          Pulse_Syntax_Base.initializer1 = initializer1;
          Pulse_Syntax_Base.body4 = uu___2;_}
        -> Pulse_RuntimeUtils.range_of_term initializer1
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
                match post_hint with
                | FStar_Pervasives_Native.None ->
                    Pulse_Typing_Env.fail g
                      (FStar_Pervasives_Native.Some (head_range t))
                      "Allocating a mutable local variable expects an annotated post-condition"
                | FStar_Pervasives_Native.Some
                    { Pulse_Typing.g = uu___;
                      Pulse_Typing.effect_annot =
                        Pulse_Syntax_Base.EffectAnnotGhost uu___1;
                      Pulse_Typing.effect_annot_typing = uu___2;
                      Pulse_Typing.ret_ty = uu___3; Pulse_Typing.u = uu___4;
                      Pulse_Typing.ty_typing = uu___5;
                      Pulse_Typing.post = uu___6; Pulse_Typing.x = uu___7;
                      Pulse_Typing.post_typing_src = uu___8;
                      Pulse_Typing.post_typing = uu___9;_}
                    ->
                    Pulse_Typing_Env.fail g
                      (FStar_Pervasives_Native.Some (head_range t))
                      "Allocating a mutable local variable is only allowed in non-ghost and non-atomic code"
                | FStar_Pervasives_Native.Some
                    { Pulse_Typing.g = uu___;
                      Pulse_Typing.effect_annot =
                        Pulse_Syntax_Base.EffectAnnotAtomic uu___1;
                      Pulse_Typing.effect_annot_typing = uu___2;
                      Pulse_Typing.ret_ty = uu___3; Pulse_Typing.u = uu___4;
                      Pulse_Typing.ty_typing = uu___5;
                      Pulse_Typing.post = uu___6; Pulse_Typing.x = uu___7;
                      Pulse_Typing.post_typing_src = uu___8;
                      Pulse_Typing.post_typing = uu___9;_}
                    ->
                    Pulse_Typing_Env.fail g
                      (FStar_Pervasives_Native.Some (head_range t))
                      "Allocating a mutable local variable is only allowed in non-ghost and non-atomic code"
                | FStar_Pervasives_Native.Some post ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Pulse.Checker.WithLocal.fst"
                               (Prims.of_int (74)) (Prims.of_int (12))
                               (Prims.of_int (74)) (Prims.of_int (52)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Pulse.Checker.WithLocal.fst"
                               (Prims.of_int (74)) (Prims.of_int (55))
                               (Prims.of_int (134)) (Prims.of_int (63)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            Pulse_Checker_Pure.push_context "check_withlocal"
                              t.Pulse_Syntax_Base.range1 g))
                      (fun uu___ ->
                         (fun g1 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithLocal.fst"
                                          (Prims.of_int (75))
                                          (Prims.of_int (56))
                                          (Prims.of_int (75))
                                          (Prims.of_int (62)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithLocal.fst"
                                          (Prims.of_int (74))
                                          (Prims.of_int (55))
                                          (Prims.of_int (134))
                                          (Prims.of_int (63)))))
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ -> t.Pulse_Syntax_Base.term1))
                                 (fun uu___ ->
                                    (fun uu___ ->
                                       match uu___ with
                                       | Pulse_Syntax_Base.Tm_WithLocal
                                           {
                                             Pulse_Syntax_Base.binder2 =
                                               binder;
                                             Pulse_Syntax_Base.initializer1 =
                                               init;
                                             Pulse_Syntax_Base.body4 = body;_}
                                           ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.WithLocal.fst"
                                                         (Prims.of_int (76))
                                                         (Prims.of_int (64))
                                                         (Prims.of_int (87))
                                                         (Prims.of_int (85)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.WithLocal.fst"
                                                         (Prims.of_int (75))
                                                         (Prims.of_int (65))
                                                         (Prims.of_int (134))
                                                         (Prims.of_int (63)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.WithLocal.fst"
                                                               (Prims.of_int (78))
                                                               (Prims.of_int (15))
                                                               (Prims.of_int (78))
                                                               (Prims.of_int (31)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.WithLocal.fst"
                                                               (Prims.of_int (79))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (87))
                                                               (Prims.of_int (85)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___1 ->
                                                            binder.Pulse_Syntax_Base.binder_ty))
                                                      (fun uu___1 ->
                                                         (fun ty ->
                                                            match Pulse_Syntax_Pure.inspect_term
                                                                    ty
                                                            with
                                                            | Pulse_Syntax_Pure.Tm_Unknown
                                                                ->
                                                                Obj.magic
                                                                  (Pulse_Checker_Pure.compute_tot_term_type_and_u
                                                                    g1 init)
                                                            | uu___1 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    g1 ty))
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term
                                                                    g1 init
                                                                    FStar_TypeChecker_Core.E_Total
                                                                    ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (init1,
                                                                    init_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (init1,
                                                                    u, ty,
                                                                    (), ())))))
                                                                    uu___2)))
                                                           uu___1)))
                                                (fun uu___1 ->
                                                   (fun uu___1 ->
                                                      match uu___1 with
                                                      | FStar_Pervasives.Mkdtuple5
                                                          (init1, init_u,
                                                           init_t,
                                                           init_t_typing,
                                                           init_typing)
                                                          ->
                                                          if
                                                            Prims.op_Negation
                                                              (Pulse_Syntax_Base.eq_univ
                                                                 init_u
                                                                 Pulse_Syntax_Pure.u0)
                                                          then
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (40)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (5)))))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (94))
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
                                                                    init1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_withlocal: allocating a local variable: type "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " is not universe zero (computed "))
                                                                    (Prims.strcat
                                                                    x ")")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    (Pulse_Syntax_Printer.univ_to_string
                                                                    init_u)))))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (head_range
                                                                    t))
                                                                    uu___2))
                                                                    uu___2))
                                                          else
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (21)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (6))
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (121)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (121)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (120)))))
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
                                                                    "withlocal: "
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
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    uu___3))
                                                                    uu___3))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (37))
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    binder.Pulse_Syntax_Base.binder_ppname
                                                                    (Pulse_Typing.mk_ref
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.comp_withlocal_body_pre
                                                                    pre
                                                                    init_t
                                                                    x_tm
                                                                    init1))
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (79))
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    post))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post1 ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    post1.Pulse_Typing.post)
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (extend_post_hint_for_local
                                                                    g1 post1
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (119)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (57)))))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    opened_body
                                                                    x))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
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
                                                                    (post1.Pulse_Typing.post)
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun c ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.post_hint_typing
                                                                    g1 post1
                                                                    x))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    post_typing_rec
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.intro_comp_typing
                                                                    g1 c ()
                                                                    post_typing_rec.Pulse_Typing.effect_annot_typing1
                                                                    () x ()))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_WithLocal
                                                                    (g1,
                                                                    (binder.Pulse_Syntax_Base.binder_ppname),
                                                                    init1,
                                                                    body1,
                                                                    init_t,
                                                                    c, x, (),
                                                                    (),
                                                                    c_typing,
                                                                    body_typing)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wrst
                                                                    c
                                                                    (Pulse_Syntax_Base.Tm_WithLocal
                                                                    {
                                                                    Pulse_Syntax_Base.binder2
                                                                    =
                                                                    (Pulse_Syntax_Base.mk_binder_ppname
                                                                    (Pulse_Typing.mk_ref
                                                                    init_t)
                                                                    binder.Pulse_Syntax_Base.binder_ppname);
                                                                    Pulse_Syntax_Base.initializer1
                                                                    = init1;
                                                                    Pulse_Syntax_Base.body4
                                                                    = body1
                                                                    })), c,
                                                                    d))
                                                                    res_ppname))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                     uu___1))) uu___))) uu___)