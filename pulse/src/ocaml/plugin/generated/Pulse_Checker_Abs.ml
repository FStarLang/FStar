open Prims
let (debug_abs :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun s ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "pulse.abs"
           then
             Obj.magic
               (Obj.repr
                  (let uu___ = s () in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                              (Prims.of_int (40)) (Prims.of_int (15))
                              (Prims.of_int (40)) (Prims.of_int (21)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                              (Prims.of_int (40)) (Prims.of_int (7))
                              (Prims.of_int (40)) (Prims.of_int (21)))))
                     (Obj.magic uu___)
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___1))
                          uu___1)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let rec (arrow_of_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      ((Pulse_Syntax_Base.term * Pulse_Syntax_Base.st_term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun env ->
    fun prog ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> prog.Pulse_Syntax_Base.term1)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                 (Prims.of_int (46)) (Prims.of_int (44)) (Prims.of_int (46))
                 (Prims.of_int (53)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                 (Prims.of_int (46)) (Prims.of_int (3)) (Prims.of_int (101))
                 (Prims.of_int (5))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | Pulse_Syntax_Base.Tm_Abs
                  { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                    Pulse_Syntax_Base.ascription = ascription;
                    Pulse_Syntax_Base.body = body;_}
                  ->
                  let uu___2 =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___3 -> Pulse_Typing_Env.fresh env)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                (Prims.of_int (47)) (Prims.of_int (12))
                                (Prims.of_int (47)) (Prims.of_int (21)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                (Prims.of_int (47)) (Prims.of_int (24))
                                (Prims.of_int (101)) (Prims.of_int (5)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun x ->
                             let uu___3 =
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___4 ->
                                       ((b.Pulse_Syntax_Base.binder_ppname),
                                         x))) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Abs.fst"
                                           (Prims.of_int (48))
                                           (Prims.of_int (13))
                                           (Prims.of_int (48))
                                           (Prims.of_int (31)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Abs.fst"
                                           (Prims.of_int (48))
                                           (Prims.of_int (34))
                                           (Prims.of_int (101))
                                           (Prims.of_int (5)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun px ->
                                        let uu___4 =
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___5 ->
                                                  Pulse_Typing_Env.push_binding
                                                    env x
                                                    (FStar_Pervasives_Native.fst
                                                       px)
                                                    b.Pulse_Syntax_Base.binder_ty)) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Abs.fst"
                                                      (Prims.of_int (49))
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (49))
                                                      (Prims.of_int (53)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Abs.fst"
                                                      (Prims.of_int (49))
                                                      (Prims.of_int (56))
                                                      (Prims.of_int (101))
                                                      (Prims.of_int (5)))))
                                             (Obj.magic uu___4)
                                             (fun uu___5 ->
                                                (fun env1 ->
                                                   let uu___5 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___6 ->
                                                             Pulse_Syntax_Naming.open_st_term_nv
                                                               body px)) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Abs.fst"
                                                                 (Prims.of_int (50))
                                                                 (Prims.of_int (15))
                                                                 (Prims.of_int (50))
                                                                 (Prims.of_int (38)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Abs.fst"
                                                                 (Prims.of_int (50))
                                                                 (Prims.of_int (41))
                                                                 (Prims.of_int (101))
                                                                 (Prims.of_int (5)))))
                                                        (Obj.magic uu___5)
                                                        (fun uu___6 ->
                                                           (fun body1 ->
                                                              let uu___6 =
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ascription.Pulse_Syntax_Base.annotated)) in
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (36)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (5)))))
                                                                   (Obj.magic
                                                                    uu___6)
                                                                   (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    annot ->
                                                                    let uu___7
                                                                    =
                                                                    if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    ascription.Pulse_Syntax_Base.elaborated
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    env1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (prog.Pulse_Syntax_Base.range1))
                                                                    "Unexpected elaborated annotation on function"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    if
                                                                    Pulse_Syntax_Base.uu___is_Tm_Abs
                                                                    body1.Pulse_Syntax_Base.term1
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match annot
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    arrow_of_abs
                                                                    env1
                                                                    body1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (arr,
                                                                    body2) ->
                                                                    ((Pulse_Syntax_Pure.tm_arrow
                                                                    b q
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    arr x))),
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body2 x)
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.effect_tag)
                                                                    })))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    c ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax_Naming.open_comp_with
                                                                    c
                                                                    (Pulse_Syntax_Pure.term_of_nvar
                                                                    px))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun c1
                                                                    ->
                                                                    match c1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_Tot
                                                                    tannot ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    ((Pulse_Syntax_Pure.tm_arrow
                                                                    b q
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    (Pulse_RuntimeUtils.hnf_lax
                                                                    (Pulse_Typing.elab_env
                                                                    env1)
                                                                    tannot) x))),
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.annotated
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c1 x));
                                                                    Pulse_Syntax_Base.elaborated
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    };
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body1 x)
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.effect_tag)
                                                                    }))))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    Pulse_Syntax_Printer.comp_to_string
                                                                    c1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    "Unexpected type of abstraction: "
                                                                    (Prims.strcat
                                                                    uu___13
                                                                    ""))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    env1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (prog.Pulse_Syntax_Base.range1))
                                                                    uu___12))
                                                                    uu___12))))
                                                                    uu___10)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match annot
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    env1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (prog.Pulse_Syntax_Base.range1))
                                                                    "Unannotated function body")
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    c ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    ((Pulse_Syntax_Pure.tm_arrow
                                                                    b q c),
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    Pulse_Syntax_Base.empty_ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body1 x)
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (prog.Pulse_Syntax_Base.effect_tag)
                                                                    }))))))
                                                                    uu___8)))
                                                                    uu___7)))
                                                             uu___6))) uu___5)))
                                       uu___4))) uu___3))) uu___1)
let (qualifier_compat :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.range ->
      Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
        FStar_Reflection_V2_Data.aqualv ->
          (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun r ->
               fun q ->
                 fun q' ->
                   match (q, q') with
                   | (FStar_Pervasives_Native.None,
                      FStar_Reflection_V2_Data.Q_Explicit) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> ())))
                   | (FStar_Pervasives_Native.Some
                      (Pulse_Syntax_Base.Implicit),
                      FStar_Reflection_V2_Data.Q_Implicit) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> ())))
                   | (FStar_Pervasives_Native.Some
                      (Pulse_Syntax_Base.Implicit),
                      FStar_Reflection_V2_Data.Q_Meta uu___) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> ())))
                   | (FStar_Pervasives_Native.Some (Pulse_Syntax_Base.TcArg),
                      FStar_Reflection_V2_Data.Q_Meta uu___) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> ())))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (Pulse_Typing_Env.fail g
                               (FStar_Pervasives_Native.Some r)
                               "Unexpected binder qualifier"))) uu___3 uu___2
            uu___1 uu___
let rec (rebuild_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      FStar_Tactics_NamedView.term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun annot ->
        let uu___ =
          debug_abs g
            (fun uu___1 ->
               let uu___2 = FStar_Tactics_V2_Builtins.term_to_string annot in
               FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                          (Prims.of_int (116)) (Prims.of_int (16))
                          (Prims.of_int (116)) (Prims.of_int (40)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                          (Prims.of_int (114)) (Prims.of_int (26))
                          (Prims.of_int (116)) (Prims.of_int (40)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       let uu___4 =
                         let uu___5 =
                           Pulse_Syntax_Printer.st_term_to_string t in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Abs.fst"
                                    (Prims.of_int (115)) (Prims.of_int (16))
                                    (Prims.of_int (115)) (Prims.of_int (39)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "FStar.Printf.fst"
                                    (Prims.of_int (122)) (Prims.of_int (8))
                                    (Prims.of_int (124)) (Prims.of_int (44)))))
                           (Obj.magic uu___5)
                           (fun uu___6 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___7 ->
                                   fun x ->
                                     Prims.strcat
                                       (Prims.strcat "rebuild_abs\n\t"
                                          (Prims.strcat uu___6 "\n\t"))
                                       (Prims.strcat x "\n"))) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Abs.fst"
                                     (Prims.of_int (114)) (Prims.of_int (26))
                                     (Prims.of_int (116)) (Prims.of_int (40)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Abs.fst"
                                     (Prims.of_int (114)) (Prims.of_int (26))
                                     (Prims.of_int (116)) (Prims.of_int (40)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___6 -> uu___5 uu___3)))) uu___3)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (114)) (Prims.of_int (4))
                   (Prims.of_int (116)) (Prims.of_int (41)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (117)) (Prims.of_int (4))
                   (Prims.of_int (166)) (Prims.of_int (47)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match ((t.Pulse_Syntax_Base.term1),
                        (FStar_Reflection_V2_Builtins.inspect_ln annot))
                with
                | (Pulse_Syntax_Base.Tm_Abs
                   { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                     Pulse_Syntax_Base.ascription = asc;
                     Pulse_Syntax_Base.body = body;_},
                   FStar_Reflection_V2_Data.Tv_Arrow (b', c')) ->
                    let uu___2 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___3 ->
                              FStar_Reflection_V2_Builtins.inspect_binder b')) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (119)) (Prims.of_int (15))
                                  (Prims.of_int (119)) (Prims.of_int (34)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (120)) (Prims.of_int (6))
                                  (Prims.of_int (160)) (Prims.of_int (41)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun b'1 ->
                               let uu___3 =
                                 qualifier_compat g
                                   (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.range
                                   q b'1.FStar_Reflection_V2_Data.qual in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (120))
                                             (Prims.of_int (6))
                                             (Prims.of_int (120))
                                             (Prims.of_int (56)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (120))
                                             (Prims.of_int (57))
                                             (Prims.of_int (160))
                                             (Prims.of_int (41)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          let uu___5 =
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___6 ->
                                                    b'1.FStar_Reflection_V2_Data.sort2)) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Abs.fst"
                                                        (Prims.of_int (121))
                                                        (Prims.of_int (15))
                                                        (Prims.of_int (121))
                                                        (Prims.of_int (22)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Abs.fst"
                                                        (Prims.of_int (121))
                                                        (Prims.of_int (25))
                                                        (Prims.of_int (160))
                                                        (Prims.of_int (41)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  (fun ty ->
                                                     let uu___6 =
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___7 ->
                                                               FStar_Reflection_V2_Builtins.inspect_comp
                                                                 c')) in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Abs.fst"
                                                                   (Prims.of_int (122))
                                                                   (Prims.of_int (17))
                                                                   (Prims.of_int (122))
                                                                   (Prims.of_int (34)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Abs.fst"
                                                                   (Prims.of_int (123))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (160))
                                                                   (Prims.of_int (41)))))
                                                          (Obj.magic uu___6)
                                                          (fun uu___7 ->
                                                             (fun comp ->
                                                                match comp
                                                                with
                                                                | FStar_Reflection_V2_Data.C_Total
                                                                    res_ty ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    Pulse_Syntax_Base.uu___is_Tm_Abs
                                                                    body.Pulse_Syntax_Base.term1
                                                                    then
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Syntax_Base.mk_binder_with_attrs
                                                                    ty
                                                                    b.Pulse_Syntax_Base.binder_ppname
                                                                    b.Pulse_Syntax_Base.binder_attrs)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun b1
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    rebuild_abs
                                                                    g body
                                                                    res_ty in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b1;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.annotated
                                                                    =
                                                                    (asc.Pulse_Syntax_Base.annotated);
                                                                    Pulse_Syntax_Base.elaborated
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    };
                                                                    Pulse_Syntax_Base.body
                                                                    = body1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (t.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (t.Pulse_Syntax_Base.effect_tag)
                                                                    }))))
                                                                    uu___8))
                                                                    else
                                                                    Obj.repr
                                                                    (match 
                                                                    Pulse_Readback.readback_comp
                                                                    res_ty
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_V2_Builtins.term_to_string
                                                                    res_ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    "Expected a computation type; got "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    ""))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    res_ty))
                                                                    uu___9))
                                                                    uu___9))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    ty1) ->
                                                                    Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    FStar_Tactics_NamedView.inspect
                                                                    res_ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Tv_Arrow
                                                                    (b1,
                                                                    uu___10)
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStar_Tactics_V2_Derived.binder_to_string
                                                                    b1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (90)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    "Expected a binder for "
                                                                    (Prims.strcat
                                                                    uu___13
                                                                    ""))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (91)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    uu___12))
                                                                    uu___12))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    ty1) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    "Incorrect annotation on function body, expected a stateful computation type; got: "
                                                                    (Prims.strcat
                                                                    uu___13
                                                                    ""))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    uu___12))
                                                                    uu___12)))
                                                                    uu___9))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    c ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    =
                                                                    (Pulse_Syntax_Base.mk_binder_with_attrs
                                                                    ty
                                                                    b.Pulse_Syntax_Base.binder_ppname
                                                                    b.Pulse_Syntax_Base.binder_attrs);
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.annotated
                                                                    =
                                                                    (asc.Pulse_Syntax_Base.annotated);
                                                                    Pulse_Syntax_Base.elaborated
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    c)
                                                                    };
                                                                    Pulse_Syntax_Base.body
                                                                    = body
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (t.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (t.Pulse_Syntax_Base.effect_tag)
                                                                    })))))
                                                                | uu___7 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_V2_Builtins.term_to_string
                                                                    annot in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    "Unexpected type of abstraction: "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    ""))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___9))
                                                                    uu___9))))
                                                               uu___7)))
                                                    uu___6))) uu___4)))
                              uu___3))
                | uu___2 ->
                    let uu___3 =
                      let uu___4 =
                        FStar_Tactics_V2_Builtins.term_to_string annot in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                 (Prims.of_int (166)) (Prims.of_int (22))
                                 (Prims.of_int (166)) (Prims.of_int (46)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___6 ->
                                Prims.strcat
                                  "Unexpected arity of abstraction: expected a term of type "
                                  (Prims.strcat uu___5 ""))) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (165)) (Prims.of_int (16))
                                  (Prims.of_int (166)) (Prims.of_int (47)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (164)) (Prims.of_int (6))
                                  (Prims.of_int (166)) (Prims.of_int (47)))))
                         (Obj.magic uu___3)
                         (fun uu___4 ->
                            (fun uu___4 ->
                               Obj.magic
                                 (Pulse_Typing_Env.fail g
                                    (FStar_Pervasives_Native.Some
                                       (t.Pulse_Syntax_Base.range1)) uu___4))
                              uu___4))) uu___1)
let (preprocess_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      let uu___ = arrow_of_abs g t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                 (Prims.of_int (172)) (Prims.of_int (19))
                 (Prims.of_int (172)) (Prims.of_int (35)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                 (Prims.of_int (172)) (Prims.of_int (3)) (Prims.of_int (177))
                 (Prims.of_int (7))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (annot, t1) ->
                  let uu___2 =
                    debug_abs g
                      (fun uu___3 ->
                         let uu___4 =
                           Pulse_Syntax_Printer.term_to_string annot in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Abs.fst"
                                    (Prims.of_int (173)) (Prims.of_int (63))
                                    (Prims.of_int (173)) (Prims.of_int (87)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Prims.fst"
                                    (Prims.of_int (611)) (Prims.of_int (19))
                                    (Prims.of_int (611)) (Prims.of_int (31)))))
                           (Obj.magic uu___4)
                           (fun uu___5 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___6 ->
                                   Prims.strcat "arrow_of_abs = "
                                     (Prims.strcat uu___5 "\n")))) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                (Prims.of_int (173)) (Prims.of_int (4))
                                (Prims.of_int (173)) (Prims.of_int (88)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                (Prims.of_int (173)) (Prims.of_int (89))
                                (Prims.of_int (177)) (Prims.of_int (7)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             let uu___4 =
                               Pulse_Checker_Pure.instantiate_term_implicits
                                 g annot FStar_Pervasives_Native.None in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Abs.fst"
                                           (Prims.of_int (174))
                                           (Prims.of_int (19))
                                           (Prims.of_int (174))
                                           (Prims.of_int (77)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Abs.fst"
                                           (Prims.of_int (173))
                                           (Prims.of_int (89))
                                           (Prims.of_int (177))
                                           (Prims.of_int (7)))))
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     (fun uu___5 ->
                                        match uu___5 with
                                        | (annot1, uu___6) ->
                                            let uu___7 =
                                              rebuild_abs g t1 annot1 in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Abs.fst"
                                                          (Prims.of_int (175))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (175))
                                                          (Prims.of_int (35)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Abs.fst"
                                                          (Prims.of_int (176))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (177))
                                                          (Prims.of_int (7)))))
                                                 (Obj.magic uu___7)
                                                 (fun uu___8 ->
                                                    (fun abs ->
                                                       let uu___8 =
                                                         debug_abs g
                                                           (fun uu___9 ->
                                                              let uu___10 =
                                                                Pulse_Syntax_Printer.st_term_to_string
                                                                  abs in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (87)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                (Obj.magic
                                                                   uu___10)
                                                                (fun uu___11
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Prims.strcat
                                                                    "rebuild_abs = "
                                                                    (Prims.strcat
                                                                    uu___11
                                                                    "\n")))) in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (88)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (11)))))
                                                            (Obj.magic uu___8)
                                                            (fun uu___9 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___10
                                                                    -> abs))))
                                                      uu___8))) uu___5)))
                            uu___3))) uu___1)
let sub_effect_comp :
  'uuuuu .
    Pulse_Typing_Env.env ->
      'uuuuu ->
        Pulse_Syntax_Base.comp_ascription ->
          Pulse_Syntax_Base.comp ->
            ((Pulse_Syntax_Base.comp,
               (unit, unit, unit) Pulse_Typing.lift_comp) Prims.dtuple2
               FStar_Pervasives_Native.option,
              unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun r ->
               fun asc ->
                 fun c_computed ->
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           match asc.Pulse_Syntax_Base.elaborated with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some c ->
                               (match (c_computed, c) with
                                | (Pulse_Syntax_Base.C_Tot t1,
                                   Pulse_Syntax_Base.C_Tot t2) ->
                                    FStar_Pervasives_Native.None
                                | (Pulse_Syntax_Base.C_ST uu___1,
                                   Pulse_Syntax_Base.C_ST uu___2) ->
                                    FStar_Pervasives_Native.None
                                | (Pulse_Syntax_Base.C_STGhost
                                   (uu___1, uu___2),
                                   Pulse_Syntax_Base.C_STGhost
                                   (uu___3, uu___4)) ->
                                    FStar_Pervasives_Native.None
                                | (Pulse_Syntax_Base.C_STAtomic
                                   (i, Pulse_Syntax_Base.Neutral, c1),
                                   Pulse_Syntax_Base.C_STGhost
                                   (uu___1, uu___2)) ->
                                    FStar_Pervasives_Native.Some
                                      (Prims.Mkdtuple2
                                         ((Pulse_Syntax_Base.C_STGhost
                                             (i, c1)),
                                           (Pulse_Typing.Lift_Neutral_Ghost
                                              (g, c_computed))))
                                | (Pulse_Syntax_Base.C_STAtomic (i, o1, c1),
                                   Pulse_Syntax_Base.C_STAtomic (j, o2, c2))
                                    ->
                                    if Pulse_Typing.sub_observability o1 o2
                                    then
                                      FStar_Pervasives_Native.Some
                                        (Prims.Mkdtuple2
                                           ((Pulse_Syntax_Base.C_STAtomic
                                               (i, o2, c1)),
                                             (Pulse_Typing.Lift_Observability
                                                (g, c_computed, o2))))
                                    else FStar_Pervasives_Native.None
                                | uu___1 -> FStar_Pervasives_Native.None))))
            uu___3 uu___2 uu___1 uu___
let (check_effect_annotation :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.range ->
      Pulse_Syntax_Base.comp_ascription ->
        Pulse_Syntax_Base.comp ->
          ((Pulse_Syntax_Base.comp, (unit, unit, unit) Pulse_Typing.st_sub)
             Prims.dtuple2,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun r ->
      fun asc ->
        fun c_computed ->
          let uu___ =
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    Prims.Mkdtuple2
                      (c_computed, (Pulse_Typing.STS_Refl (g, c_computed))))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                     (Prims.of_int (201)) (Prims.of_int (12))
                     (Prims.of_int (201)) (Prims.of_int (42)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                     (Prims.of_int (202)) (Prims.of_int (2))
                     (Prims.of_int (251)) (Prims.of_int (7)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun nop ->
                  match asc.Pulse_Syntax_Base.elaborated with
                  | FStar_Pervasives_Native.None ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> nop)))
                  | FStar_Pervasives_Native.Some c ->
                      Obj.magic
                        (Obj.repr
                           (match (c, c_computed) with
                            | (Pulse_Syntax_Base.C_Tot uu___1,
                               Pulse_Syntax_Base.C_Tot uu___2) ->
                                Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> nop))
                            | (Pulse_Syntax_Base.C_ST uu___1,
                               Pulse_Syntax_Base.C_ST uu___2) ->
                                Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> nop))
                            | (Pulse_Syntax_Base.C_STGhost (i, c1),
                               Pulse_Syntax_Base.C_STGhost (j, c2)) ->
                                Obj.repr
                                  (if Pulse_Syntax_Base.eq_tm i j
                                   then
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> nop))
                                   else
                                     Obj.repr
                                       (let uu___2 =
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  Pulse_Syntax_Base.mk_binder
                                                    "res" FStar_Range.range_0
                                                    c2.Pulse_Syntax_Base.res)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (220))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (220))
                                                   (Prims.of_int (50)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (220))
                                                   (Prims.of_int (53))
                                                   (Prims.of_int (242))
                                                   (Prims.of_int (20)))))
                                          (Obj.magic uu___2)
                                          (fun uu___3 ->
                                             (fun b ->
                                                let uu___3 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___4 ->
                                                          Pulse_Typing.tm_inames_subset
                                                            j i)) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (221))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (221))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (221))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (242))
                                                              (Prims.of_int (20)))))
                                                     (Obj.magic uu___3)
                                                     (fun uu___4 ->
                                                        (fun phi ->
                                                           let uu___4 =
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___5
                                                                    -> ())) in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (48)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (20)))))
                                                                (Obj.magic
                                                                   uu___4)
                                                                (fun uu___5
                                                                   ->
                                                                   (fun
                                                                    typing ->
                                                                    let uu___5
                                                                    =
                                                                    FStar_Tactics_V2_Derived.with_policy
                                                                    FStar_Tactics_Types.ForceSMT
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Checker_Pure.try_check_prop_validity
                                                                    g phi ()) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun tok
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    tok
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    i in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Annotated effect expects only invariants in")
                                                                    uu___11)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    j in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (93)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "to be opened; but computed effect claims that invariants")
                                                                    uu___14)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___13
                                                                    (Pulse_PP.text
                                                                    "are opened"))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___10
                                                                    uu___12))))
                                                                    uu___10) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    [uu___9])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    i))
                                                                    uu___8))
                                                                    uu___8)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match tok
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tok1 ->
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    ((match c_computed
                                                                    with
                                                                    | Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___9,
                                                                    obs,
                                                                    uu___10)
                                                                    ->
                                                                    Pulse_Typing.STS_AtomicInvs
                                                                    (g, c2,
                                                                    j, i,
                                                                    obs, obs,
                                                                    ())
                                                                    | Pulse_Syntax_Base.C_STGhost
                                                                    (uu___9,
                                                                    uu___10)
                                                                    ->
                                                                    Pulse_Typing.STS_GhostInvs
                                                                    (g, c2,
                                                                    j, i, ()))))))))
                                                                    uu___6)))
                                                                    uu___5)))
                                                          uu___4))) uu___3)))
                            | (Pulse_Syntax_Base.C_STAtomic
                               (i, Pulse_Syntax_Base.Observable, c1),
                               Pulse_Syntax_Base.C_STAtomic
                               (j, Pulse_Syntax_Base.Observable, c2)) ->
                                Obj.repr
                                  (if Pulse_Syntax_Base.eq_tm i j
                                   then
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> nop))
                                   else
                                     Obj.repr
                                       (let uu___2 =
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  Pulse_Syntax_Base.mk_binder
                                                    "res" FStar_Range.range_0
                                                    c2.Pulse_Syntax_Base.res)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (220))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (220))
                                                   (Prims.of_int (50)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (220))
                                                   (Prims.of_int (53))
                                                   (Prims.of_int (242))
                                                   (Prims.of_int (20)))))
                                          (Obj.magic uu___2)
                                          (fun uu___3 ->
                                             (fun b ->
                                                let uu___3 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___4 ->
                                                          Pulse_Typing.tm_inames_subset
                                                            j i)) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (221))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (221))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (221))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (242))
                                                              (Prims.of_int (20)))))
                                                     (Obj.magic uu___3)
                                                     (fun uu___4 ->
                                                        (fun phi ->
                                                           let uu___4 =
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___5
                                                                    -> ())) in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (48)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (20)))))
                                                                (Obj.magic
                                                                   uu___4)
                                                                (fun uu___5
                                                                   ->
                                                                   (fun
                                                                    typing ->
                                                                    let uu___5
                                                                    =
                                                                    FStar_Tactics_V2_Derived.with_policy
                                                                    FStar_Tactics_Types.ForceSMT
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Checker_Pure.try_check_prop_validity
                                                                    g phi ()) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun tok
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    tok
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    i in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Annotated effect expects only invariants in")
                                                                    uu___11)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    j in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (93)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "to be opened; but computed effect claims that invariants")
                                                                    uu___14)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___13
                                                                    (Pulse_PP.text
                                                                    "are opened"))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___10
                                                                    uu___12))))
                                                                    uu___10) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    [uu___9])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    i))
                                                                    uu___8))
                                                                    uu___8)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match tok
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tok1 ->
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    ((match c_computed
                                                                    with
                                                                    | Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___9,
                                                                    obs,
                                                                    uu___10)
                                                                    ->
                                                                    Pulse_Typing.STS_AtomicInvs
                                                                    (g, c2,
                                                                    j, i,
                                                                    obs, obs,
                                                                    ())
                                                                    | Pulse_Syntax_Base.C_STGhost
                                                                    (uu___9,
                                                                    uu___10)
                                                                    ->
                                                                    Pulse_Typing.STS_GhostInvs
                                                                    (g, c2,
                                                                    j, i, ()))))))))
                                                                    uu___6)))
                                                                    uu___5)))
                                                          uu___4))) uu___3)))
                            | (uu___1, uu___2) ->
                                Obj.repr
                                  (let uu___3 =
                                     let uu___4 =
                                       let uu___5 =
                                         let uu___6 =
                                           let uu___7 =
                                             Pulse_Syntax_Printer.tag_of_comp
                                               c in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Abs.fst"
                                                      (Prims.of_int (248))
                                                      (Prims.of_int (40))
                                                      (Prims.of_int (248))
                                                      (Prims.of_int (57)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Abs.fst"
                                                      (Prims.of_int (248))
                                                      (Prims.of_int (22))
                                                      (Prims.of_int (248))
                                                      (Prims.of_int (58)))))
                                             (Obj.magic uu___7)
                                             (fun uu___8 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___9 ->
                                                     FStar_Pprint.arbitrary_string
                                                       uu___8)) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Abs.fst"
                                                    (Prims.of_int (248))
                                                    (Prims.of_int (22))
                                                    (Prims.of_int (248))
                                                    (Prims.of_int (58)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Abs.fst"
                                                    (Prims.of_int (247))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (248))
                                                    (Prims.of_int (58)))))
                                           (Obj.magic uu___6)
                                           (fun uu___7 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___8 ->
                                                   FStar_Pprint.prefix
                                                     (Prims.of_int (4))
                                                     Prims.int_one
                                                     (Pulse_PP.text
                                                        "Expected effect")
                                                     uu___7)) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Abs.fst"
                                                  (Prims.of_int (247))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (248))
                                                  (Prims.of_int (58)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Abs.fst"
                                                  (Prims.of_int (247))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (250))
                                                  (Prims.of_int (67)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            (fun uu___6 ->
                                               let uu___7 =
                                                 let uu___8 =
                                                   let uu___9 =
                                                     Pulse_Syntax_Printer.tag_of_comp
                                                       c_computed in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (250))
                                                              (Prims.of_int (40))
                                                              (Prims.of_int (250))
                                                              (Prims.of_int (66)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (250))
                                                              (Prims.of_int (22))
                                                              (Prims.of_int (250))
                                                              (Prims.of_int (67)))))
                                                     (Obj.magic uu___9)
                                                     (fun uu___10 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___11 ->
                                                             FStar_Pprint.arbitrary_string
                                                               uu___10)) in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Abs.fst"
                                                            (Prims.of_int (250))
                                                            (Prims.of_int (22))
                                                            (Prims.of_int (250))
                                                            (Prims.of_int (67)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Abs.fst"
                                                            (Prims.of_int (249))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (250))
                                                            (Prims.of_int (67)))))
                                                   (Obj.magic uu___8)
                                                   (fun uu___9 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___10 ->
                                                           FStar_Pprint.prefix
                                                             (Prims.of_int (4))
                                                             Prims.int_one
                                                             (Pulse_PP.text
                                                                "but this function body has effect")
                                                             uu___9)) in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Abs.fst"
                                                             (Prims.of_int (249))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (250))
                                                             (Prims.of_int (67)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Abs.fst"
                                                             (Prims.of_int (247))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (250))
                                                             (Prims.of_int (67)))))
                                                    (Obj.magic uu___7)
                                                    (fun uu___8 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___9 ->
                                                            FStar_Pprint.op_Hat_Slash_Hat
                                                              uu___6 uu___8))))
                                              uu___6) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Abs.fst"
                                                (Prims.of_int (247))
                                                (Prims.of_int (8))
                                                (Prims.of_int (250))
                                                (Prims.of_int (67)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Abs.fst"
                                                (Prims.of_int (246))
                                                (Prims.of_int (26))
                                                (Prims.of_int (251))
                                                (Prims.of_int (7)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___6 -> [uu___5])) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Abs.fst"
                                              (Prims.of_int (246))
                                              (Prims.of_int (26))
                                              (Prims.of_int (251))
                                              (Prims.of_int (7)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Abs.fst"
                                              (Prims.of_int (246))
                                              (Prims.of_int (6))
                                              (Prims.of_int (251))
                                              (Prims.of_int (7)))))
                                     (Obj.magic uu___3)
                                     (fun uu___4 ->
                                        (fun uu___4 ->
                                           Obj.magic
                                             (Pulse_Typing_Env.fail_doc g
                                                (FStar_Pervasives_Native.Some
                                                   r) uu___4)) uu___4)))))
                 uu___1)
let (maybe_rewrite_body_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.comp_ascription ->
            ((Pulse_Syntax_Base.comp,
               (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g ->
               fun e ->
                 fun c ->
                   fun d ->
                     fun asc ->
                       match asc.Pulse_Syntax_Base.annotated with
                       | FStar_Pervasives_Native.None ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ -> Prims.Mkdtuple2 (c, d))))
                       | FStar_Pervasives_Native.Some
                           (Pulse_Syntax_Base.C_Tot t) ->
                           Obj.magic
                             (Obj.repr
                                (match c with
                                 | Pulse_Syntax_Base.C_Tot t' ->
                                     let uu___ =
                                       Pulse_Checker_Pure.instantiate_term_implicits
                                         g t FStar_Pervasives_Native.None in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Abs.fst"
                                                (Prims.of_int (265))
                                                (Prims.of_int (19))
                                                (Prims.of_int (265))
                                                (Prims.of_int (73)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Abs.fst"
                                                (Prims.of_int (264))
                                                (Prims.of_int (20))
                                                (Prims.of_int (278))
                                                (Prims.of_int (7)))))
                                       (Obj.magic uu___)
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             match uu___1 with
                                             | (t1, uu___2) ->
                                                 let uu___3 =
                                                   Pulse_Checker_Pure.check_universe
                                                     g t1 in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Abs.fst"
                                                               (Prims.of_int (266))
                                                               (Prims.of_int (32))
                                                               (Prims.of_int (266))
                                                               (Prims.of_int (69)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Abs.fst"
                                                               (Prims.of_int (265))
                                                               (Prims.of_int (76))
                                                               (Prims.of_int (277))
                                                               (Prims.of_int (26)))))
                                                      (Obj.magic uu___3)
                                                      (fun uu___4 ->
                                                         (fun uu___4 ->
                                                            match uu___4 with
                                                            | Prims.Mkdtuple2
                                                                (u, t_typing)
                                                                ->
                                                                let uu___5 =
                                                                  Pulse_Checker_Base.norm_st_typing_inverse
                                                                    g e t' d
                                                                    u t1 ()
                                                                    [FStar_Pervasives.hnf;
                                                                    FStar_Pervasives.delta] in
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e.Pulse_Syntax_Base.range1))
                                                                    "Inferred type is incompatible with annotation")
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    d1 ->
                                                                    let uu___7
                                                                    =
                                                                    debug_abs
                                                                    g
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    t1) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    Pulse_Syntax_Printer.comp_to_string
                                                                    c in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "maybe_rewrite_body_typing:{\nfrom "
                                                                    (Prims.strcat
                                                                    uu___13
                                                                    "\nto "))
                                                                    (Prims.strcat
                                                                    x "}\n"))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    uu___12
                                                                    uu___10))))
                                                                    uu___10)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_Tot
                                                                    t1), d1)))))
                                                                    uu___6)))
                                                           uu___4))) uu___1)
                                 | uu___ ->
                                     Pulse_Typing_Env.fail g
                                       (FStar_Pervasives_Native.Some
                                          (e.Pulse_Syntax_Base.range1))
                                       "Inferred type is incompatible with annotation"))
                       | FStar_Pervasives_Native.Some c1 ->
                           Obj.magic
                             (Obj.repr
                                (let uu___ =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 ->
                                           Pulse_Syntax_Base.st_comp_of_comp
                                             c1)) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Abs.fst"
                                            (Prims.of_int (283))
                                            (Prims.of_int (15))
                                            (Prims.of_int (283))
                                            (Prims.of_int (32)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Abs.fst"
                                            (Prims.of_int (284))
                                            (Prims.of_int (6))
                                            (Prims.of_int (284))
                                            (Prims.of_int (92)))))
                                   (Obj.magic uu___)
                                   (fun uu___1 ->
                                      (fun st ->
                                         Obj.magic
                                           (Pulse_Typing_Env.fail g
                                              (FStar_Pervasives_Native.Some
                                                 (Pulse_RuntimeUtils.range_of_term
                                                    st.Pulse_Syntax_Base.pre))
                                              "Unexpected annotation on a function body"))
                                        uu___1)))) uu___4 uu___3 uu___2
              uu___1 uu___
let (open_ascription :
  Pulse_Syntax_Base.comp_ascription ->
    Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.comp_ascription)
  =
  fun c ->
    fun nv ->
      let t = Pulse_Syntax_Pure.term_of_nvar nv in
      Pulse_Syntax_Naming.subst_ascription c
        [FStar_Reflection_Typing.DT (Prims.int_zero, t)]
let (close_ascription :
  Pulse_Syntax_Base.comp_ascription ->
    Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.comp_ascription)
  =
  fun c ->
    fun nv ->
      Pulse_Syntax_Naming.subst_ascription c
        [FStar_Reflection_Typing.ND
           ((FStar_Pervasives_Native.snd nv), Prims.int_zero)]
let rec (check_abs_core :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Checker_Base.check_t ->
        ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
           (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun check ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> t.Pulse_Syntax_Base.range1)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (299)) (Prims.of_int (14))
                   (Prims.of_int (299)) (Prims.of_int (21)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (300)) (Prims.of_int (2))
                   (Prims.of_int (434)) (Prims.of_int (29)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun range ->
                match t.Pulse_Syntax_Base.term1 with
                | Pulse_Syntax_Base.Tm_Abs
                    {
                      Pulse_Syntax_Base.b =
                        { Pulse_Syntax_Base.binder_ty = t1;
                          Pulse_Syntax_Base.binder_ppname = ppname;
                          Pulse_Syntax_Base.binder_attrs = binder_attrs;_};
                      Pulse_Syntax_Base.q = qual;
                      Pulse_Syntax_Base.ascription = asc;
                      Pulse_Syntax_Base.body = body;_}
                    ->
                    let uu___1 =
                      Pulse_Checker_Pure.compute_tot_term_type g t1 in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (303)) (Prims.of_int (24))
                                  (Prims.of_int (303)) (Prims.of_int (49)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (301)) (Prims.of_int (99))
                                  (Prims.of_int (434)) (Prims.of_int (29)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun uu___2 ->
                               match uu___2 with
                               | FStar_Pervasives.Mkdtuple3
                                   (t2, uu___3, uu___4) ->
                                   let uu___5 =
                                     Pulse_Checker_Pure.check_universe g t2 in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (304))
                                                 (Prims.of_int (28))
                                                 (Prims.of_int (304))
                                                 (Prims.of_int (46)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (303))
                                                 (Prims.of_int (52))
                                                 (Prims.of_int (434))
                                                 (Prims.of_int (29)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           (fun uu___6 ->
                                              match uu___6 with
                                              | Prims.Mkdtuple2 (u, t_typing)
                                                  ->
                                                  let uu___7 =
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___8 ->
                                                            Pulse_Typing_Env.fresh
                                                              g)) in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Abs.fst"
                                                                (Prims.of_int (305))
                                                                (Prims.of_int (12))
                                                                (Prims.of_int (305))
                                                                (Prims.of_int (19)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Abs.fst"
                                                                (Prims.of_int (305))
                                                                (Prims.of_int (22))
                                                                (Prims.of_int (434))
                                                                (Prims.of_int (29)))))
                                                       (Obj.magic uu___7)
                                                       (fun uu___8 ->
                                                          (fun x ->
                                                             let uu___8 =
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    (ppname,
                                                                    x))) in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (22)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                  (Obj.magic
                                                                    uu___8)
                                                                  (fun uu___9
                                                                    ->
                                                                    (fun px
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax_Pure.tm_var
                                                                    {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    = ppname
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun var
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    ppname t2)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun g'
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body px)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    body_opened
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    open_ascription
                                                                    asc px)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun asc1
                                                                    ->
                                                                    match 
                                                                    body_opened.Pulse_Syntax_Base.term1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Abs
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    check_abs_core
                                                                    g'
                                                                    body_opened
                                                                    check in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    sub_effect_comp
                                                                    g'
                                                                    body1.Pulse_Syntax_Base.range1
                                                                    asc1
                                                                    c_body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    match uu___18
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (c_body,
                                                                    body_typing)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    lift)) ->
                                                                    Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    (Pulse_Typing.T_Lift
                                                                    (g',
                                                                    body1,
                                                                    c_body,
                                                                    c_body1,
                                                                    body_typing,
                                                                    lift))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    body_typing1)
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    uu___17)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    check_effect_annotation
                                                                    g'
                                                                    body1.Pulse_Syntax_Base.range1
                                                                    asc1
                                                                    c_body1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    match uu___21
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body2,
                                                                    d_sub) ->
                                                                    let uu___22
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g',
                                                                    body1,
                                                                    c_body1,
                                                                    c_body2,
                                                                    body_typing1,
                                                                    d_sub))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    body_typing2
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    maybe_rewrite_body_typing
                                                                    g' body1
                                                                    c_body2
                                                                    body_typing2
                                                                    asc1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body3,
                                                                    body_typing3)
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    body1 x)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    body_closed
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_Tactics_Unseal.unseal
                                                                    binder_attrs in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (92)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun attr
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    Pulse_Checker_Pure.instantiate_term_implicits
                                                                    g attr
                                                                    FStar_Pervasives_Native.None in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (91)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___31)))
                                                                    uu___29))
                                                                    uu___29) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Sealed.seal
                                                                    uu___28)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    binder_attrs1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wtag
                                                                    FStar_Pervasives_Native.None
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs1
                                                                    };
                                                                    Pulse_Syntax_Base.q
                                                                    = qual;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    Pulse_Syntax_Base.empty_ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    body_closed
                                                                    })),
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    (Pulse_Syntax_Pure.tm_arrow
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs1
                                                                    } qual
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c_body3 x))),
                                                                    (Pulse_Typing.T_Abs
                                                                    (g, x,
                                                                    qual,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs1
                                                                    }, u,
                                                                    body_closed,
                                                                    c_body3,
                                                                    (),
                                                                    body_typing3)))))))
                                                                    uu___26)))
                                                                    uu___24)))
                                                                    uu___23)))
                                                                    uu___21)))
                                                                    uu___19)))
                                                                    uu___17)))
                                                                    uu___15))
                                                                    | 
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    match 
                                                                    asc1.Pulse_Syntax_Base.elaborated
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    "Missing annotation on a function body"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    r) ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    r) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Prims.strcat
                                                                    "Incorrect annotation on a function, expected a computation type, got: "
                                                                    (Prims.strcat
                                                                    uu___17
                                                                    ""))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    uu___16))
                                                                    uu___16)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    c ->
                                                                    let uu___15
                                                                    =
                                                                    if
                                                                    (Pulse_Syntax_Base.uu___is_C_STGhost
                                                                    c) ||
                                                                    (Pulse_Syntax_Base.uu___is_C_STAtomic
                                                                    c)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c) px)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    inames ->
                                                                    let uu___17
                                                                    =
                                                                    FStar_Tactics_V2_Builtins.norm_well_typed_term
                                                                    (Pulse_Typing.elab_env
                                                                    g)
                                                                    [FStar_Pervasives.primops;
                                                                    FStar_Pervasives.iota;
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.delta_attr
                                                                    ["Pulse.Lib.Core.unfold_check_opens"]]
                                                                    inames in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    inames1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    inames1))))
                                                                    uu___17)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Pulse_Syntax_Pure.tm_emp_inames))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    inames_opened
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    ((match c
                                                                    with
                                                                    | Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___17,
                                                                    obs, st)
                                                                    ->
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (inames_opened,
                                                                    obs, st)
                                                                    | Pulse_Syntax_Base.C_STGhost
                                                                    (uu___17,
                                                                    st) ->
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (inames_opened,
                                                                    st)
                                                                    | uu___17
                                                                    -> c),
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c) px),
                                                                    inames_opened,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c) px)),
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_term'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c) var
                                                                    Prims.int_one))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    (elab_c,
                                                                    pre_opened,
                                                                    inames_opened,
                                                                    ret_ty,
                                                                    post_hint_body)
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    Pulse_Checker_Pure.check_slprop
                                                                    g'
                                                                    pre_opened in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (pre_opened1,
                                                                    pre_typing)
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Pulse_Syntax_Naming.close_term
                                                                    pre_opened1
                                                                    x)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun pre
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    match post_hint_body
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range1))
                                                                    [
                                                                    Pulse_PP.text
                                                                    "Top-level functions must be annotated with pre and post conditions"]
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    let uu___20
                                                                    =
                                                                    Pulse_Checker_Base.intro_post_hint
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "post_hint_typing"
                                                                    range g')
                                                                    (Pulse_Syntax_Base.effect_annot_of_comp
                                                                    elab_c)
                                                                    ret_ty
                                                                    post in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    post_hint_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    post_hint_typing)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun post
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_fret")) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    ppname_ret
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    check g'
                                                                    pre_opened1
                                                                    () post
                                                                    ppname_ret
                                                                    body_opened in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun r ->
                                                                    let uu___22
                                                                    =
                                                                    Pulse_Checker_Base.apply_checker_result_k
                                                                    g'
                                                                    pre_opened1
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    post) r
                                                                    ppname_ret in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    uu___23)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    {
                                                                    Pulse_Syntax_Base.annotated
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.elaborated
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_comp_nv
                                                                    elab_c px))
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    c_opened
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    sub_effect_comp
                                                                    g'
                                                                    body1.Pulse_Syntax_Base.range1
                                                                    c_opened
                                                                    c_body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    match uu___29
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (c_body,
                                                                    body_typing)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    lift)) ->
                                                                    Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    (Pulse_Typing.T_Lift
                                                                    (g',
                                                                    body1,
                                                                    c_body,
                                                                    c_body1,
                                                                    body_typing,
                                                                    lift))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body1,
                                                                    body_typing1)
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    uu___28)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    check_effect_annotation
                                                                    g'
                                                                    body1.Pulse_Syntax_Base.range1
                                                                    c_opened
                                                                    c_body1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    match uu___32
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body2,
                                                                    d_sub) ->
                                                                    let uu___33
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g',
                                                                    body1,
                                                                    c_body1,
                                                                    c_body2,
                                                                    body_typing1,
                                                                    d_sub))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    body_typing2
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    maybe_rewrite_body_typing
                                                                    g' body1
                                                                    c_body2
                                                                    body_typing2
                                                                    asc1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    match uu___35
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_body3,
                                                                    body_typing3)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wtag
                                                                    FStar_Pervasives_Native.None
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs
                                                                    };
                                                                    Pulse_Syntax_Base.q
                                                                    = qual;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    Pulse_Syntax_Base.empty_ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body1 x)
                                                                    })),
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    (Pulse_Syntax_Pure.tm_arrow
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs
                                                                    } qual
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c_body3 x))),
                                                                    (Pulse_Typing.T_Abs
                                                                    (g, x,
                                                                    qual,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    binder_attrs
                                                                    }, u,
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body1 x),
                                                                    c_body3,
                                                                    (),
                                                                    body_typing3)))))))
                                                                    uu___34)))
                                                                    uu___32)))
                                                                    uu___30)))
                                                                    uu___28)))
                                                                    uu___27)))
                                                                    uu___25)))
                                                                    uu___23)))
                                                                    uu___22)))
                                                                    uu___21)))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___17)))
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                            uu___8))) uu___6)))
                              uu___2))) uu___1)
let (check_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Checker_Base.check_t ->
        ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
           (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun check ->
        let uu___ = preprocess_abs g t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (438)) (Prims.of_int (10))
                   (Prims.of_int (438)) (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (439)) (Prims.of_int (2))
                   (Prims.of_int (439)) (Prims.of_int (26)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun t1 -> Obj.magic (check_abs_core g t1 check)) uu___1)