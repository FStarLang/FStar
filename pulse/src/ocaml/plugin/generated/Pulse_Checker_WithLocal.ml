open Prims
let (extend_post_hint_for_local :
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
              (Pulse_Typing.comp_withlocal_body_post p.Pulse_Typing.post
                 init_t (Pulse_Syntax_Pure.null_var x));
            Pulse_Typing.post_typing = ()
          }

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
                        (FStar_Range.mk_range "Pulse.Checker.WithLocal.fst"
                           (Prims.of_int (35)) (Prims.of_int (10))
                           (Prims.of_int (35)) (Prims.of_int (50)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithLocal.fst"
                           (Prims.of_int (35)) (Prims.of_int (53))
                           (Prims.of_int (92)) (Prims.of_int (38)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Checker_Pure.push_context "check_withlocal"
                          t.Pulse_Syntax_Base.range2 g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.WithLocal.fst"
                                      (Prims.of_int (36)) (Prims.of_int (16))
                                      (Prims.of_int (36)) (Prims.of_int (42)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.WithLocal.fst"
                                      (Prims.of_int (36)) (Prims.of_int (47))
                                      (Prims.of_int (92)) (Prims.of_int (38)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   fun t0 ->
                                     {
                                       Pulse_Syntax_Base.term1 = t0;
                                       Pulse_Syntax_Base.range2 =
                                         (t.Pulse_Syntax_Base.range2)
                                     }))
                             (fun uu___ ->
                                (fun wr ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.WithLocal.fst"
                                                 (Prims.of_int (37))
                                                 (Prims.of_int (54))
                                                 (Prims.of_int (37))
                                                 (Prims.of_int (60)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.WithLocal.fst"
                                                 (Prims.of_int (36))
                                                 (Prims.of_int (47))
                                                 (Prims.of_int (92))
                                                 (Prims.of_int (38)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___ ->
                                              t.Pulse_Syntax_Base.term1))
                                        (fun uu___ ->
                                           (fun uu___ ->
                                              match uu___ with
                                              | Pulse_Syntax_Base.Tm_WithLocal
                                                  {
                                                    Pulse_Syntax_Base.binder1
                                                      = binder;
                                                    Pulse_Syntax_Base.initializer1
                                                      = init;
                                                    Pulse_Syntax_Base.body4 =
                                                      body;_}
                                                  ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithLocal.fst"
                                                                (Prims.of_int (39))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (39))
                                                                (Prims.of_int (34)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithLocal.fst"
                                                                (Prims.of_int (37))
                                                                (Prims.of_int (63))
                                                                (Prims.of_int (92))
                                                                (Prims.of_int (38)))))
                                                       (Obj.magic
                                                          (Pulse_Checker_Pure.check_tot_term_and_type
                                                             g1 init))
                                                       (fun uu___1 ->
                                                          (fun uu___1 ->
                                                             match uu___1
                                                             with
                                                             | FStar_Pervasives.Mkdtuple5
                                                                 (init1,
                                                                  init_u,
                                                                  init_t,
                                                                  init_t_typing,
                                                                  init_typing)
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ((binder.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
                                                                    (fun
                                                                    uu___2 ->
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
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (119)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (119)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (118)))))
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
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "withlocal: "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " is free in body")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range2))
                                                                    uu___2))
                                                                    uu___2))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Pure.term_of_nvar
                                                                    px))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun x_tm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    binder.Pulse_Syntax_Base.binder_ppname
                                                                    (Pulse_Typing.mk_ref
                                                                    init_t)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    g_extended
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.comp_withlocal_body_pre
                                                                    pre
                                                                    init_t
                                                                    x_tm
                                                                    init1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body_pre
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body_pre_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (103)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (87))
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
                                                                    uu___3 ->
                                                                    post)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Allocating a mutable local variable expects an annotated post-condition")))
                                                                    (fun
                                                                    uu___3 ->
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    extend_post_hint_for_local
                                                                    g1 post
                                                                    init_t x))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body_post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (117)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (66))
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
                                                                    uu___4 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g_extended
                                                                    body_pre
                                                                    body_post
                                                                    r
                                                                    binder.Pulse_Syntax_Base.binder_ppname))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (73))
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
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "check_withlocal: body computation type "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    " is not ST")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range2))
                                                                    uu___5))
                                                                    uu___5))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (87))
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
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (87))
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
                                                                    (post.Pulse_Typing.post)
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
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (100)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (100)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.post_hint_typing
                                                                    g1 post x))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    post_typing_rec
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.intro_comp_typing
                                                                    g1 c ()
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
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_WithLocal
                                                                    (g1,
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
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_WithLocal
                                                                    {
                                                                    Pulse_Syntax_Base.binder1
                                                                    =
                                                                    (Pulse_Typing.as_binder
                                                                    (Pulse_Typing.mk_ref
                                                                    init_t));
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
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2))
                                                                 else
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (91))
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
                                                                    init1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_withlocal: allocating a local variable: type "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " is not universe zero (computed "))
                                                                    (Prims.strcat
                                                                    x ")")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    (Pulse_Syntax_Printer.univ_to_string
                                                                    init_u)))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    uu___3))
                                                                    uu___3)))
                                                            uu___1))) uu___)))
                                  uu___))) uu___)