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
                     (Prims.of_int (100)) (Prims.of_int (56)))
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
                                (Prims.of_int (100)) (Prims.of_int (56)))
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
                                               (Prims.of_int (41))
                                               (Prims.of_int (90)))
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.While.fst"
                                               (Prims.of_int (39))
                                               (Prims.of_int (66))
                                               (Prims.of_int (100))
                                               (Prims.of_int (56)))
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
                                                      (match ex_inv with
                                                       | Pulse_Syntax_Base.Tm_ExistsSL
                                                           (u, ty, inv1,
                                                            uu___2)
                                                           ->
                                                           Obj.magic
                                                             (Obj.repr
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
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    while_cond_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1) u ty
                                                                    inv1 ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    while_cond_comp_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (93)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
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
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
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
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Checker_Common.post_hint_from_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1)
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv1)
                                                                    while_cond_comp_typing1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    while_cond_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (69)))
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
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
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
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (79)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    while_body_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1) u ty
                                                                    inv1 ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    while_body_comp_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (95)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
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
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
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
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Checker_Common.post_hint_from_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    g1)
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv1)
                                                                    while_body_comp_typing1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    while_post_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (76)))
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
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
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
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (79)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Typing.T_While
                                                                    (g1,
                                                                    inv1,
                                                                    cond1,
                                                                    body1,
                                                                    (),
                                                                    cond_typing,
                                                                    body_typing)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (63)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.try_frame_pre
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
                                                                    inv1) d))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
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
                                                                    uu___8
                                                                    post_hint
                                                                    true))
                                                                    uu___8)))
                                                                    uu___8))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (75)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Typing.comp_while_body
                                                                    inv1)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (63)))
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
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Could not prove the inferred type of the while body matches the annotation\nInferred type = "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    "\nAnnotated type = "))
                                                                    (Prims.strcat
                                                                    x2 "\n")))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    uu___10
                                                                    uu___9))))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___9)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___6))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Typing.comp_while_cond
                                                                    inv1)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (56)))
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
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Could not prove that the inferred type of the while condition matches the annotation\nInferred type = "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\nAnnotated type = "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
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
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___7)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4))))
                                                       | uu___2 ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Derived.fail
                                                                   "Typechecked invariant is not an exists"))))
                                                 uu___1))) uu___))) uu___)