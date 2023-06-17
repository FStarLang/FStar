open Prims
type ('p, 'x, 't, 'u, 'post) post_hint_compatible = Obj.t
let (check_admit :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Checker_Common.post_hint_opt ->
            ((unit, unit, unit) Pulse_Checker_Common.checker_result_t, 
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "Pulse.Checker.Admit.fst"
                 (Prims.of_int (29)) (Prims.of_int (43)) (Prims.of_int (29))
                 (Prims.of_int (49)))
              (FStar_Range.mk_range "Pulse.Checker.Admit.fst"
                 (Prims.of_int (28)) (Prims.of_int (46)) (Prims.of_int (71))
                 (Prims.of_int (4)))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> t.Pulse_Syntax_Base.term1))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | Pulse_Syntax_Base.Tm_Admit
                        { Pulse_Syntax_Base.ctag1 = c;
                          Pulse_Syntax_Base.u1 = uu___1;
                          Pulse_Syntax_Base.typ = t1;
                          Pulse_Syntax_Base.post3 = post;_}
                        ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Checker.Admit.fst"
                                (Prims.of_int (30)) (Prims.of_int (10))
                                (Prims.of_int (30)) (Prims.of_int (17)))
                             (FStar_Range.mk_range "Pulse.Checker.Admit.fst"
                                (Prims.of_int (30)) (Prims.of_int (20))
                                (Prims.of_int (71)) (Prims.of_int (4)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> Pulse_Typing_Env.fresh g))
                             (fun uu___2 ->
                                (fun x ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Admit.fst"
                                           (Prims.of_int (31))
                                           (Prims.of_int (11))
                                           (Prims.of_int (31))
                                           (Prims.of_int (20)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Admit.fst"
                                           (Prims.of_int (31))
                                           (Prims.of_int (23))
                                           (Prims.of_int (71))
                                           (Prims.of_int (4)))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              Pulse_Syntax_Base.v_as_nv x))
                                        (fun uu___2 ->
                                           (fun px ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Admit.fst"
                                                      (Prims.of_int (38))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (60))
                                                      (Prims.of_int (9)))
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Admit.fst"
                                                      (Prims.of_int (61))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (71))
                                                      (Prims.of_int (4)))
                                                   (match (post, post_hint)
                                                    with
                                                    | (FStar_Pervasives_Native.None,
                                                       FStar_Pervasives_Native.None)
                                                        ->
                                                        Obj.magic
                                                          (Pulse_Typing_Env.fail
                                                             g
                                                             FStar_Pervasives_Native.None
                                                             "T_Admit: either no post or two posts")
                                                    | (FStar_Pervasives_Native.Some
                                                       uu___2,
                                                       FStar_Pervasives_Native.Some
                                                       uu___3) ->
                                                        Obj.magic
                                                          (Pulse_Typing_Env.fail
                                                             g
                                                             FStar_Pervasives_Native.None
                                                             "T_Admit: either no post or two posts")
                                                    | (FStar_Pervasives_Native.Some
                                                       post1, uu___2) ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Admit.fst"
                                                                (Prims.of_int (44))
                                                                (Prims.of_int (32))
                                                                (Prims.of_int (44))
                                                                (Prims.of_int (50)))
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Admit.fst"
                                                                (Prims.of_int (43))
                                                                (Prims.of_int (23))
                                                                (Prims.of_int (49))
                                                                (Prims.of_int (49)))
                                                             (Obj.magic
                                                                (Pulse_Checker_Pure.check_universe
                                                                   g t1))
                                                             (fun uu___3 ->
                                                                (fun uu___3
                                                                   ->
                                                                   match uu___3
                                                                   with
                                                                   | 
                                                                   Prims.Mkdtuple2
                                                                    (u,
                                                                    t_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (49)))
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
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (83)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (49)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x t1)
                                                                    post_opened
                                                                    Pulse_Syntax_Base.Tm_VProp))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post2,
                                                                    post_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (t1, u,
                                                                    (),
                                                                    post2,
                                                                    ())))))
                                                                    uu___4)))
                                                                  uu___3))
                                                    | (uu___2,
                                                       FStar_Pervasives_Native.Some
                                                       post1) ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Admit.fst"
                                                                (Prims.of_int (52))
                                                                (Prims.of_int (33))
                                                                (Prims.of_int (52))
                                                                (Prims.of_int (37)))
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Admit.fst"
                                                                (Prims.of_int (53))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (60))
                                                                (Prims.of_int (9)))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   -> post1))
                                                             (fun uu___3 ->
                                                                (fun post2 ->
                                                                   if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    post2.Pulse_Checker_Common.post)
                                                                   then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Unexpected freevar clash in Tm_Admit"))
                                                                   else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    ((post2.Pulse_Checker_Common.ret_ty),
                                                                    (post2.Pulse_Checker_Common.u),
                                                                    (),
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    post2.Pulse_Checker_Common.post
                                                                    px), ())))))
                                                                  uu___3)))
                                                   (fun res ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           match res with
                                                           | FStar_Pervasives.Mkdtuple5
                                                               (t2, u,
                                                                t_typing,
                                                                post_opened,
                                                                post_typing)
                                                               ->
                                                               FStar_Pervasives.Mkdtuple3
                                                                 ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Admit
                                                                    {
                                                                    Pulse_Syntax_Base.ctag1
                                                                    = c;
                                                                    Pulse_Syntax_Base.u1
                                                                    =
                                                                    ({
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t2;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x)
                                                                    }.Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.typ
                                                                    =
                                                                    ({
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t2;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x)
                                                                    }.Pulse_Syntax_Base.res);
                                                                    Pulse_Syntax_Base.post3
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                   (Pulse_Typing.comp_admit
                                                                    c
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t2;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x)
                                                                    }),
                                                                   (Pulse_Typing.T_Admit
                                                                    (g,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t2;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x)
                                                                    }, c,
                                                                    (Pulse_Typing.STC
                                                                    (g,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t2;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x)
                                                                    }, x, (),
                                                                    (), ())))))))))
                                             uu___2))) uu___2))) uu___)