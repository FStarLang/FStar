open Prims
let (while_cond_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.ppname ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            unit -> (unit, unit) Pulse_Typing_Metatheory.comp_typing_u)
  =
  fun g ->
    fun u ->
      fun x ->
        fun ty ->
          fun inv_body ->
            fun inv_typing ->
              Pulse_Typing_Metatheory.admit_comp_typing g
                (Pulse_Typing.comp_while_cond x inv_body)
let (while_body_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.ppname ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            unit -> (unit, unit) Pulse_Typing_Metatheory.comp_typing_u)
  =
  fun g ->
    fun u ->
      fun x ->
        fun ty ->
          fun inv_body ->
            fun inv_typing ->
              Pulse_Typing_Metatheory.admit_comp_typing g
                (Pulse_Typing.comp_while_body x inv_body)
let (check_while :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Typing.post_hint_opt ->
            Pulse_Checker_Base.check_t ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun check ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.While.fst"
                         (Prims.of_int (37)) (Prims.of_int (10))
                         (Prims.of_int (37)) (Prims.of_int (45)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.While.fst"
                         (Prims.of_int (37)) (Prims.of_int (48))
                         (Prims.of_int (103)) (Prims.of_int (70)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Checker_Pure.push_context "while loop"
                        t.Pulse_Syntax_Base.range2 g))
                (fun uu___ ->
                   (fun g1 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.While.fst"
                                    (Prims.of_int (38)) (Prims.of_int (72))
                                    (Prims.of_int (38)) (Prims.of_int (78)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.While.fst"
                                    (Prims.of_int (37)) (Prims.of_int (48))
                                    (Prims.of_int (103)) (Prims.of_int (70)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> t.Pulse_Syntax_Base.term1))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | Pulse_Syntax_Base.Tm_While
                                     { Pulse_Syntax_Base.invariant = inv;
                                       Pulse_Syntax_Base.condition = cond;
                                       Pulse_Syntax_Base.condition_var =
                                         condition_var;
                                       Pulse_Syntax_Base.body3 = body;_}
                                     ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.While.fst"
                                                   (Prims.of_int (40))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (41))
                                                   (Prims.of_int (88)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.While.fst"
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (81))
                                                   (Prims.of_int (103))
                                                   (Prims.of_int (70)))))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.check_vprop
                                                (Pulse_Checker_Pure.push_context
                                                   "invariant"
                                                   (Pulse_Syntax_Base.term_range
                                                      inv) g1)
                                                (Pulse_Syntax_Base.tm_exists_sl
                                                   Pulse_Syntax_Pure.u0
                                                   {
                                                     Pulse_Syntax_Base.binder_ty
                                                       = Pulse_Typing.tm_bool;
                                                     Pulse_Syntax_Base.binder_ppname
                                                       = condition_var
                                                   } inv)))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | Prims.Mkdtuple2
                                                    (ex_inv, inv_typing) ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.While.fst"
                                                                  (Prims.of_int (44))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (45))
                                                                  (Prims.of_int (59)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.While.fst"
                                                                  (Prims.of_int (45))
                                                                  (Prims.of_int (60))
                                                                  (Prims.of_int (103))
                                                                  (Prims.of_int (70)))))
                                                         (if
                                                            Prims.op_Negation
                                                              (Pulse_Syntax_Base.uu___is_Tm_ExistsSL
                                                                 ex_inv.Pulse_Syntax_Base.t)
                                                          then
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Typechecked invariant is not an exists"))
                                                          else
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    ()))))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (67)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ex_inv.Pulse_Syntax_Base.t))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = ty;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = nm;_},
                                                                    inv1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
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
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (nm.Pulse_Syntax_Base.range))
                                                                    "While loop invariant exists but its witness type is not bool"))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    while_cond_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Base.term_range
                                                                    inv) g1)
                                                                    u nm ty
                                                                    inv1 ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    while_cond_comp_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Base.term_range
                                                                    inv) g1)
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1))
                                                                    (Pulse_Typing_Metatheory.comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Base.term_range
                                                                    inv) g1)
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1)
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Checker_Base.post_hint_from_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Base.term_range
                                                                    inv) g1)
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1)
                                                                    while_cond_comp_typing1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    while_cond_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (check
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "while condition"
                                                                    cond.Pulse_Syntax_Base.range2
                                                                    g1)
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1))
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    while_cond_hint)
                                                                    cond))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "while condition"
                                                                    cond.Pulse_Syntax_Base.range2
                                                                    g1)
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1))
                                                                    while_cond_hint
                                                                    r))
                                                                    uu___6)))
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
                                                                    nm inv1)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    while_body_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Base.term_range
                                                                    inv) g1)
                                                                    u nm ty
                                                                    inv1 ()))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    while_body_comp_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Base.term_range
                                                                    inv) g1)
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1))
                                                                    (Pulse_Typing_Metatheory.comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Base.term_range
                                                                    inv) g1)
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1)
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Checker_Base.post_hint_from_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Base.term_range
                                                                    inv) g1)
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1)
                                                                    while_body_comp_typing1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    while_post_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (check
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "while body"
                                                                    body.Pulse_Syntax_Base.range2
                                                                    g1)
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1))
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    while_post_hint)
                                                                    body))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "while body"
                                                                    body.Pulse_Syntax_Base.range2
                                                                    g1)
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1))
                                                                    while_post_hint
                                                                    r))
                                                                    uu___8)))
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
                                                                    nm inv1)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (59)))))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover.try_frame_pre
                                                                    g pre ()
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_While
                                                                    {
                                                                    Pulse_Syntax_Base.invariant
                                                                    = inv1;
                                                                    Pulse_Syntax_Base.condition
                                                                    = cond1;
                                                                    Pulse_Syntax_Base.condition_var
                                                                    =
                                                                    Pulse_Syntax_Base.ppname_default;
                                                                    Pulse_Syntax_Base.body3
                                                                    = body1
                                                                    }))
                                                                    (Pulse_Typing.comp_while
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    inv1) d))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Pulse_Prover.repack
                                                                    g pre
                                                                    uu___9
                                                                    post_hint
                                                                    t.Pulse_Syntax_Base.range2))
                                                                    uu___9)))
                                                                    uu___9))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
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
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___10))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___7))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
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
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___8))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                              uu___2)))
                                               uu___1))) uu___))) uu___)