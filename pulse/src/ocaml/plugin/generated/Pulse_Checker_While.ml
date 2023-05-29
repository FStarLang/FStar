open Prims
let (while_cond_comp_typing :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          unit -> (unit, unit) Pulse_Typing_Metatheory.comp_typing_u)
  =
  fun g ->
    fun u ->
      fun ty ->
        fun inv_body ->
          fun inv_typing ->
            Pulse_Typing_Metatheory.admit_comp_typing g
              (Pulse_Typing.comp_while_cond inv_body)
let (while_body_comp_typing :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          unit -> (unit, unit) Pulse_Typing_Metatheory.comp_typing_u)
  =
  fun g ->
    fun u ->
      fun ty ->
        fun inv_body ->
          fun inv_typing ->
            Pulse_Typing_Metatheory.admit_comp_typing g
              (Pulse_Typing.comp_while_body inv_body)
let (check_while :
  Prims.bool ->
    Pulse_Typing.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Checker_Common.post_hint_opt ->
              (Prims.bool -> Pulse_Checker_Common.check_t) ->
                ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                   (unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
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
                  (FStar_Range.mk_range "Pulse.Checker.While.fst"
                     (Prims.of_int (38)) (Prims.of_int (10))
                     (Prims.of_int (38)) (Prims.of_int (37)))
                  (FStar_Range.mk_range "Pulse.Checker.While.fst"
                     (Prims.of_int (38)) (Prims.of_int (40))
                     (Prims.of_int (106)) (Prims.of_int (59)))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Checker_Pure.push_context "while loop" g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Checker.While.fst"
                                (Prims.of_int (39)) (Prims.of_int (57))
                                (Prims.of_int (39)) (Prims.of_int (63)))
                             (FStar_Range.mk_range "Pulse.Checker.While.fst"
                                (Prims.of_int (38)) (Prims.of_int (40))
                                (Prims.of_int (106)) (Prims.of_int (59)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> t.Pulse_Syntax_Base.term1))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | Pulse_Syntax_Base.Tm_While
                                       { Pulse_Syntax_Base.invariant = inv;
                                         Pulse_Syntax_Base.condition = cond;
                                         Pulse_Syntax_Base.body3 = body;_}
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.While.fst"
                                               (Prims.of_int (41))
                                               (Prims.of_int (4))
                                               (Prims.of_int (42))
                                               (Prims.of_int (61)))
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.While.fst"
                                               (Prims.of_int (39))
                                               (Prims.of_int (66))
                                               (Prims.of_int (106))
                                               (Prims.of_int (59)))
                                            (Obj.magic
                                               (Pulse_Checker_Pure.check_vprop
                                                  (Pulse_Checker_Pure.push_context
                                                     "invariant" g1)
                                                  (Pulse_Syntax_Base.Tm_ExistsSL
                                                     (Pulse_Syntax_Pure.u0,
                                                       Pulse_Typing.tm_bool,
                                                       inv,
                                                       Pulse_Syntax_Base.should_elim_true))))
                                            (fun uu___1 ->
                                               (fun uu___1 ->
                                                  match uu___1 with
                                                  | Prims.Mkdtuple2
                                                      (ex_inv, inv_typing) ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.While.fst"
                                                              (Prims.of_int (44))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (44))
                                                              (Prims.of_int (49)))
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.While.fst"
                                                              (Prims.of_int (44))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (106))
                                                              (Prims.of_int (59)))
                                                           (Obj.magic
                                                              (Pulse_Checker_Framing.check_frameable
                                                                 g pre ()
                                                                 ex_inv))
                                                           (fun uu___2 ->
                                                              (fun uu___2 ->
                                                                 match uu___2
                                                                 with
                                                                 | FStar_Pervasives.Inr
                                                                    f ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.raise
                                                                    (Pulse_Checker_Common.Framing_failure
                                                                    f)))
                                                                 | FStar_Pervasives.Inl
                                                                    framing_token
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match ex_inv
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, ty,
                                                                    inv1,
                                                                    uu___3)
                                                                    ->
                                                                    Obj.repr
                                                                    (if
                                                                    (Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    ty
                                                                    Pulse_Typing.tm_bool))
                                                                    ||
                                                                    (Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_univ
                                                                    u
                                                                    Pulse_Syntax_Pure.u0))
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "While loop invariant is exists but its witness type is not bool")
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (79)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (74)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    while_cond_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1) u ty
                                                                    inv1 ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    while_cond_comp_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (95)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (74)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1)
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv1))
                                                                    (Pulse_Typing_Metatheory.comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1)
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv1)
                                                                    while_cond_comp_typing1)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (res_typing,
                                                                    cond_pre_typing,
                                                                    x,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (74)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Checker_Common.post_hint_from_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1)
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv1)
                                                                    while_cond_comp_typing1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    while_cond_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (74)))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "while condition"
                                                                    g1) cond
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv1)) ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    while_cond_hint)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (cond1,
                                                                    cond_comp,
                                                                    cond_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_comp
                                                                    cond_comp
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv1)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (78)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    while_body_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1) u ty
                                                                    inv1 ()))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    while_body_comp_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (97)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (78)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1)
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv1))
                                                                    (Pulse_Typing_Metatheory.comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1)
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv1)
                                                                    while_body_comp_typing1)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (res_typing1,
                                                                    body_pre_typing,
                                                                    x1,
                                                                    post_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (78)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Checker_Common.post_hint_from_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1)
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv1)
                                                                    while_body_comp_typing1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    while_post_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "while body"
                                                                    g1) body
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv1)) ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    while_post_hint)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    body_comp,
                                                                    body_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_comp
                                                                    body_comp
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv1)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Typing.T_While
                                                                    (g1,
                                                                    inv1,
                                                                    cond1,
                                                                    body1,
                                                                    (),
                                                                    cond_typing,
                                                                    body_typing)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Checker_Framing.apply_frame
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_While
                                                                    {
                                                                    Pulse_Syntax_Base.invariant
                                                                    = inv1;
                                                                    Pulse_Syntax_Base.condition
                                                                    = cond1;
                                                                    Pulse_Syntax_Base.body3
                                                                    = body1
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_while
                                                                    inv1) d
                                                                    framing_token))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c, st_d)
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.repack
                                                                    g pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_While
                                                                    {
                                                                    Pulse_Syntax_Base.invariant
                                                                    = inv1;
                                                                    Pulse_Syntax_Base.condition
                                                                    = cond1;
                                                                    Pulse_Syntax_Base.body3
                                                                    = body1
                                                                    }))
                                                                    (Prims.Mkdtuple2
                                                                    (c, st_d))
                                                                    post_hint
                                                                    true))
                                                                    uu___9)))
                                                                    uu___9))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (78)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv1)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (78)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    body_comp))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Could not prove the inferred type of the while body matches the annotation\nInferred type = "
                                                                    (Prims.strcat
                                                                    uu___11
                                                                    "\nAnnotated type = "))
                                                                    (Prims.strcat
                                                                    x2 "\n")))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    uu___11
                                                                    uu___10))))
                                                                    uu___10)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___7))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (100))
                                                                    Prims.int_zero
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (74)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (74)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (100))
                                                                    Prims.int_zero
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (74)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv1)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (100))
                                                                    Prims.int_zero
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (74)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (100))
                                                                    Prims.int_zero
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (74)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    cond_comp))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Could not prove that the inferred type of the while condition matches the annotation\nInferred type = "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    "\nAnnotated type = "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    uu___8))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Typechecked invariant is not an exists"))))
                                                                uu___2)))
                                                 uu___1))) uu___))) uu___)