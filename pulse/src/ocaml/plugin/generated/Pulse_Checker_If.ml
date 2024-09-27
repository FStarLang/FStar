open Prims
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.st_term ->
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
            fun b ->
              fun e1 ->
                fun e2 ->
                  fun check1 ->
                    let uu___ =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              Pulse_Typing_Env.push_context g "check_if"
                                e1.Pulse_Syntax_Base.range1)) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.If.fst"
                               (Prims.of_int (45)) (Prims.of_int (10))
                               (Prims.of_int (45)) (Prims.of_int (61)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.If.fst"
                               (Prims.of_int (45)) (Prims.of_int (64))
                               (Prims.of_int (105)) (Prims.of_int (43)))))
                      (Obj.magic uu___)
                      (fun uu___1 ->
                         (fun g1 ->
                            let uu___1 =
                              Pulse_Checker_Pure.check_tot_term g1 b
                                Pulse_Typing.tm_bool in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.If.fst"
                                          (Prims.of_int (48))
                                          (Prims.of_int (4))
                                          (Prims.of_int (48))
                                          (Prims.of_int (30)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.If.fst"
                                          (Prims.of_int (45))
                                          (Prims.of_int (64))
                                          (Prims.of_int (105))
                                          (Prims.of_int (43)))))
                                 (Obj.magic uu___1)
                                 (fun uu___2 ->
                                    (fun uu___2 ->
                                       match uu___2 with
                                       | Prims.Mkdtuple2 (b1, b_typing) ->
                                           let uu___3 =
                                             Obj.magic
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___4 ->
                                                     post_hint.Pulse_Typing.post)) in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (50))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (50))
                                                         (Prims.of_int (27)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (50))
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (105))
                                                         (Prims.of_int (43)))))
                                                (Obj.magic uu___3)
                                                (fun uu___4 ->
                                                   (fun post ->
                                                      let uu___4 =
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___5 ->
                                                                Pulse_Typing_Env.fresh
                                                                  g1)) in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (19)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (43)))))
                                                           (Obj.magic uu___4)
                                                           (fun uu___5 ->
                                                              (fun hyp ->
                                                                 let uu___5 =
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun eq_v
                                                                    ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 hyp
                                                                    (Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_if_hyp")
                                                                    (Pulse_Typing.mk_eq2
                                                                    Pulse_Syntax_Pure.u0
                                                                    Pulse_Typing.tm_bool
                                                                    b1 eq_v))) in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    g_with_eq
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun eq_v
                                                                    ->
                                                                    fun br ->
                                                                    fun
                                                                    is_then
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    g_with_eq
                                                                    eq_v)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    g_with_eq1
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    {
                                                                    Pulse_Syntax_Base.hint_type
                                                                    =
                                                                    (Pulse_Syntax_Base.RENAME
                                                                    {
                                                                    Pulse_Syntax_Base.pairs
                                                                    =
                                                                    [
                                                                    (b1,
                                                                    eq_v)];
                                                                    Pulse_Syntax_Base.goal
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.tac_opt
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    });
                                                                    Pulse_Syntax_Base.binders
                                                                    = [];
                                                                    Pulse_Syntax_Base.t
                                                                    = br
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (br.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (br.Pulse_Syntax_Base.effect_tag);
                                                                    Pulse_Syntax_Base.source
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    false)
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun br1
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_if_br")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    ppname ->
                                                                    let uu___13
                                                                    =
                                                                    check1
                                                                    g_with_eq1
                                                                    pre ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    ppname
                                                                    br1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g_with_eq1
                                                                    pre
                                                                    post_hint
                                                                    r ppname))
                                                                    uu___14)))
                                                                    uu___13) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br2, c,
                                                                    d) ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    if
                                                                    is_then
                                                                    then
                                                                    "then"
                                                                    else
                                                                    "else")) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    br_name
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    hyp
                                                                    (Pulse_Syntax_Naming.freevars_st
                                                                    br2)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (br2.Pulse_Syntax_Base.range1))
                                                                    (Prims.strcat
                                                                    "check_if: branch hypothesis is in freevars of checked "
                                                                    (Prims.strcat
                                                                    br_name
                                                                    " branch"))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br2, c,
                                                                    d)))))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    check_branch
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    check_branch
                                                                    Pulse_Typing.tm_true
                                                                    e1 true in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e11, c1,
                                                                    e1_typing)
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    check_branch
                                                                    Pulse_Typing.tm_false
                                                                    e2 false in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e21, c2,
                                                                    e2_typing)
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Pulse_JoinComp.join_comps
                                                                    (g_with_eq
                                                                    Pulse_Typing.tm_true)
                                                                    e11 c1
                                                                    e1_typing
                                                                    (g_with_eq
                                                                    Pulse_Typing.tm_false)
                                                                    e21 c2
                                                                    e2_typing
                                                                    post_hint in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c,
                                                                    e1_typing1,
                                                                    e2_typing1)
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Pulse_Checker_Base.comp_typing_from_post_hint
                                                                    g c ()
                                                                    post_hint in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wrst
                                                                    c
                                                                    (Pulse_Syntax_Base.Tm_If
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b1;
                                                                    Pulse_Syntax_Base.then_
                                                                    = e11;
                                                                    Pulse_Syntax_Base.else_
                                                                    = e21;
                                                                    Pulse_Syntax_Base.post1
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })), c,
                                                                    (Pulse_Typing.T_If
                                                                    (g1, b1,
                                                                    e11, e21,
                                                                    c, hyp,
                                                                    (),
                                                                    e1_typing1,
                                                                    e2_typing1,
                                                                    ()))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g1 pre
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    d
                                                                    res_ppname))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                uu___5)))
                                                     uu___4))) uu___2)))
                           uu___1)