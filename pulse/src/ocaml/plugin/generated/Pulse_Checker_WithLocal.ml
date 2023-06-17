open Prims
let (extend_post_hint_for_local :
  Pulse_Typing_Env.env ->
    unit Pulse_Checker_Common.post_hint_for_env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.var -> unit Pulse_Checker_Common.post_hint_for_env)
  =
  fun g ->
    fun p ->
      fun init_t ->
        fun x ->
          {
            Pulse_Checker_Common.g = (p.Pulse_Checker_Common.g);
            Pulse_Checker_Common.ret_ty = (p.Pulse_Checker_Common.ret_ty);
            Pulse_Checker_Common.u = (p.Pulse_Checker_Common.u);
            Pulse_Checker_Common.ty_typing = ();
            Pulse_Checker_Common.post =
              (Pulse_Typing.comp_withlocal_body_post
                 p.Pulse_Checker_Common.post init_t
                 (Pulse_Syntax_Pure.null_var x));
            Pulse_Checker_Common.post_typing = ()
          }

let (check_withlocal :
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
                  (FStar_Range.mk_range "Pulse.Checker.WithLocal.fst"
                     (Prims.of_int (38)) (Prims.of_int (10))
                     (Prims.of_int (38)) (Prims.of_int (50)))
                  (FStar_Range.mk_range "Pulse.Checker.WithLocal.fst"
                     (Prims.of_int (38)) (Prims.of_int (53))
                     (Prims.of_int (87)) (Prims.of_int (80)))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Checker_Pure.push_context "check_withlocal"
                          t.Pulse_Syntax_Base.range1 g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "Pulse.Checker.WithLocal.fst"
                                (Prims.of_int (39)) (Prims.of_int (16))
                                (Prims.of_int (39)) (Prims.of_int (42)))
                             (FStar_Range.mk_range
                                "Pulse.Checker.WithLocal.fst"
                                (Prims.of_int (39)) (Prims.of_int (47))
                                (Prims.of_int (87)) (Prims.of_int (80)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   fun t0 ->
                                     {
                                       Pulse_Syntax_Base.term1 = t0;
                                       Pulse_Syntax_Base.range1 =
                                         (t.Pulse_Syntax_Base.range1)
                                     }))
                             (fun uu___ ->
                                (fun wr ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.WithLocal.fst"
                                           (Prims.of_int (40))
                                           (Prims.of_int (54))
                                           (Prims.of_int (40))
                                           (Prims.of_int (60)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.WithLocal.fst"
                                           (Prims.of_int (39))
                                           (Prims.of_int (47))
                                           (Prims.of_int (87))
                                           (Prims.of_int (80)))
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
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithLocal.fst"
                                                          (Prims.of_int (42))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (42))
                                                          (Prims.of_int (30)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithLocal.fst"
                                                          (Prims.of_int (40))
                                                          (Prims.of_int (63))
                                                          (Prims.of_int (87))
                                                          (Prims.of_int (80)))
                                                       (Obj.magic
                                                          (Pulse_Checker_Pure.check_term_and_type
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (10)))
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (10)))
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (122)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (122)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (121)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.unseal
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
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    uu___2))
                                                                    uu___2))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (10)))
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (10)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    (Pulse_Typing.mk_ref
                                                                    init_t)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    g_extended
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (10)))
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (10)))
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (108)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (10)))
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
                                                                    post.Pulse_Checker_Common.post)
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Unexpected name clash in with_local")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (29)))
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (109)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g_extended
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body px)
                                                                    body_pre
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    body_post)))
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
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    "withlocal: body is not stt or postcondition mismatch")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (29)))
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (85)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (29)))
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
                                                                    (post.Pulse_Checker_Common.post)
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun c ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (108)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (67)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithLocal.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (108)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Checker_Common.post_hint_typing
                                                                    g1 post x))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    post_typing_rec
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.intro_comp_typing
                                                                    g1 c ()
                                                                    () x ()))
                                                                    uu___6)))
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
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
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Allocating a local variable: init type is not universe zero"))
                                                            uu___1))) uu___)))
                                  uu___))) uu___)