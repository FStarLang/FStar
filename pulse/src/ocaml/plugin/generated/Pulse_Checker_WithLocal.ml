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
            Pulse_Typing.ret_ty = (p.Pulse_Typing.ret_ty);
            Pulse_Typing.u = (p.Pulse_Typing.u);
            Pulse_Typing.ty_typing = ();
            Pulse_Typing.post =
              (Pulse_Typing.comp_withlocal_body_post p.Pulse_Typing.post
                 init_t (Pulse_Syntax_Pure.null_var x));
            Pulse_Typing.post_typing = ()
          }

let (check_withlocal :
  Prims.bool ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Typing.post_hint_opt ->
              Prims.bool ->
                (Prims.bool -> Pulse_Checker_Common.check_t) ->
                  ((unit, unit, unit, unit)
                     Pulse_Checker_Common.checker_result_t,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun frame_pre ->
                fun check' ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.WithLocal.fst"
                             (Prims.of_int (39)) (Prims.of_int (2))
                             (Prims.of_int (40)) (Prims.of_int (54)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.WithLocal.fst"
                             (Prims.of_int (40)) (Prims.of_int (55))
                             (Prims.of_int (90)) (Prims.of_int (80)))))
                    (if Prims.op_Negation frame_pre
                     then
                       FStar_Tactics_V2_Derived.fail
                         "withlocal: frame_pre is false, bailing"
                     else
                       FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
                    (fun uu___ ->
                       (fun uu___ ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithLocal.fst"
                                        (Prims.of_int (41))
                                        (Prims.of_int (10))
                                        (Prims.of_int (41))
                                        (Prims.of_int (50)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithLocal.fst"
                                        (Prims.of_int (41))
                                        (Prims.of_int (53))
                                        (Prims.of_int (90))
                                        (Prims.of_int (80)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     Pulse_Checker_Pure.push_context
                                       "check_withlocal"
                                       t.Pulse_Syntax_Base.range2 g))
                               (fun uu___1 ->
                                  (fun g1 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.WithLocal.fst"
                                                   (Prims.of_int (42))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (42))
                                                   (Prims.of_int (42)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.WithLocal.fst"
                                                   (Prims.of_int (42))
                                                   (Prims.of_int (47))
                                                   (Prims.of_int (90))
                                                   (Prims.of_int (80)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                fun t0 ->
                                                  {
                                                    Pulse_Syntax_Base.term1 =
                                                      t0;
                                                    Pulse_Syntax_Base.range2
                                                      =
                                                      (t.Pulse_Syntax_Base.range2)
                                                  }))
                                          (fun uu___1 ->
                                             (fun wr ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.WithLocal.fst"
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (54))
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (60)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.WithLocal.fst"
                                                              (Prims.of_int (42))
                                                              (Prims.of_int (47))
                                                              (Prims.of_int (90))
                                                              (Prims.of_int (80)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           t.Pulse_Syntax_Base.term1))
                                                     (fun uu___1 ->
                                                        (fun uu___1 ->
                                                           match uu___1 with
                                                           | Pulse_Syntax_Base.Tm_WithLocal
                                                               {
                                                                 Pulse_Syntax_Base.binder1
                                                                   = binder;
                                                                 Pulse_Syntax_Base.initializer1
                                                                   = init;
                                                                 Pulse_Syntax_Base.body4
                                                                   = body;_}
                                                               ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (30)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (80)))))
                                                                    (
                                                                    Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_and_type
                                                                    g1 init))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
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
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (10)))))
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (10)))))
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
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (122)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (122)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (50))
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
                                                                    (body.Pulse_Syntax_Base.range2))
                                                                    uu___3))
                                                                    uu___3))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (10)))))
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
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (10)))))
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
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (10)))))
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
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (10)))))
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
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (10)))))
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
                                                                    "Allocating a mutable local variable expects an annotated post-condition")))
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
                                                                    "Unexpected name clash in with_local")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    extend_post_hint_for_local
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (119)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g_extended
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body px)
                                                                    body_pre
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    body_post)
                                                                    frame_pre))
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
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range2))
                                                                    "withlocal: body is not stt or postcondition mismatch")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
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
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (108)))))
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
                                                                    (Pulse_Checker_Common.intro_comp_typing
                                                                    g1 c ()
                                                                    () x ()))
                                                                    uu___7)))
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives.Mkdtuple3
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
                                                                    (Pulse_Typing.T_WithLocal
                                                                    (g1,
                                                                    init1,
                                                                    body1,
                                                                    init_t,
                                                                    c, x, (),
                                                                    (),
                                                                    c_typing,
                                                                    body_typing)))))))
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
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Allocating a local variable: init type is not universe zero"))
                                                                    uu___2)))
                                                          uu___1))) uu___1)))
                                    uu___1))) uu___)