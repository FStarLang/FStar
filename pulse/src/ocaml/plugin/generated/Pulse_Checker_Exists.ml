open Prims

let (terms_to_string :
  Pulse_Syntax_Base.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
               (Prims.of_int (41)) (Prims.of_int (23)) (Prims.of_int (41))
               (Prims.of_int (68)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
               (Prims.of_int (41)) (Prims.of_int (4)) (Prims.of_int (41))
               (Prims.of_int (68))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_String.concat "\n" uu___1))
let (check_elim_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              let uu___ =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        Pulse_Typing_Env.push_context g "check_elim_exists"
                          t.Pulse_Syntax_Base.range1)) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
                         (Prims.of_int (53)) (Prims.of_int (10))
                         (Prims.of_int (53)) (Prims.of_int (69)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
                         (Prims.of_int (53)) (Prims.of_int (72))
                         (Prims.of_int (94)) (Prims.of_int (55)))))
                (Obj.magic uu___)
                (fun uu___1 ->
                   (fun g1 ->
                      let uu___1 =
                        Obj.magic
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> t.Pulse_Syntax_Base.term1)) in
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Exists.fst"
                                    (Prims.of_int (55)) (Prims.of_int (32))
                                    (Prims.of_int (55)) (Prims.of_int (38)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Exists.fst"
                                    (Prims.of_int (53)) (Prims.of_int (72))
                                    (Prims.of_int (94)) (Prims.of_int (55)))))
                           (Obj.magic uu___1)
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 match uu___2 with
                                 | Pulse_Syntax_Base.Tm_ElimExists
                                     { Pulse_Syntax_Base.p4 = t1;_} ->
                                     let uu___3 =
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               Pulse_RuntimeUtils.range_of_term
                                                 t1)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Exists.fst"
                                                   (Prims.of_int (56))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (56))
                                                   (Prims.of_int (48)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Exists.fst"
                                                   (Prims.of_int (56))
                                                   (Prims.of_int (51))
                                                   (Prims.of_int (94))
                                                   (Prims.of_int (55)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             (fun t_rng ->
                                                let uu___4 =
                                                  match Pulse_Syntax_Pure.inspect_term
                                                          t1
                                                  with
                                                  | Pulse_Syntax_Pure.Tm_Unknown
                                                      ->
                                                      let uu___5 =
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___6 ->
                                                                Pulse_Syntax_Pure.slprop_as_list
                                                                  pre)) in
                                                      FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Exists.fst"
                                                                 (Prims.of_int (61))
                                                                 (Prims.of_int (15))
                                                                 (Prims.of_int (61))
                                                                 (Prims.of_int (33)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Exists.fst"
                                                                 (Prims.of_int (61))
                                                                 (Prims.of_int (36))
                                                                 (Prims.of_int (72))
                                                                 (Prims.of_int (41)))))
                                                        (Obj.magic uu___5)
                                                        (fun uu___6 ->
                                                           (fun ts ->
                                                              let uu___6 =
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_List_Tot_Base.filter
                                                                    (fun t2
                                                                    ->
                                                                    match 
                                                                    Pulse_Syntax_Pure.inspect_term
                                                                    t2
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Pure.Tm_ExistsSL
                                                                    (uu___8,
                                                                    uu___9,
                                                                    uu___10)
                                                                    -> true
                                                                    | 
                                                                    uu___8 ->
                                                                    false) ts)) in
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (75)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (41)))))
                                                                   (Obj.magic
                                                                    uu___6)
                                                                   (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    exist_tms
                                                                    ->
                                                                    match exist_tms
                                                                    with
                                                                    | 
                                                                    one::[]
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.Mkdtuple2
                                                                    (one, ()))))
                                                                    | 
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    terms_to_string
                                                                    exist_tms in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
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
                                                                    "Could not decide which exists term to eliminate: choices are\n"
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    ""))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    t_rng)
                                                                    uu___9))
                                                                    uu___9))))
                                                                    uu___7)))
                                                             uu___6)
                                                  | uu___5 ->
                                                      let uu___6 =
                                                        Pulse_Checker_Pure.instantiate_term_implicits
                                                          g1 t1
                                                          FStar_Pervasives_Native.None in
                                                      FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Exists.fst"
                                                                 (Prims.of_int (75))
                                                                 (Prims.of_int (17))
                                                                 (Prims.of_int (75))
                                                                 (Prims.of_int (52)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Exists.fst"
                                                                 (Prims.of_int (74))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (76))
                                                                 (Prims.of_int (22)))))
                                                        (Obj.magic uu___6)
                                                        (fun uu___7 ->
                                                           (fun uu___7 ->
                                                              match uu___7
                                                              with
                                                              | (t2, uu___8)
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    Pulse_Checker_Pure.check_slprop
                                                                    g1 t2))
                                                             uu___7) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Exists.fst"
                                                              (Prims.of_int (58))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (76))
                                                              (Prims.of_int (22)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Exists.fst"
                                                              (Prims.of_int (56))
                                                              (Prims.of_int (51))
                                                              (Prims.of_int (94))
                                                              (Prims.of_int (55)))))
                                                     (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun uu___5 ->
                                                           match uu___5 with
                                                           | Prims.Mkdtuple2
                                                               (t2, t_typing)
                                                               ->
                                                               let uu___6 =
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___5)) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (55)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (55)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___6)
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Syntax_Pure.inspect_term
                                                                    t2)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun tv
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Pure.uu___is_Tm_ExistsSL
                                                                    tv)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    t2 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.strcat
                                                                    "check_elim_exists: elim_exists argument "
                                                                    (Prims.strcat
                                                                    uu___12
                                                                    " not an existential"))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    t_rng)
                                                                    uu___11))
                                                                    uu___11)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (55)))))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> tv)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (55)))))
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
                                                                    Pulse_Syntax_Pure.Tm_ExistsSL
                                                                    (u,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = ty;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = uu___13;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    = uu___14;_},
                                                                    p) ->
                                                                    let uu___15
                                                                    =
                                                                    Pulse_Checker_Pure.check_universe
                                                                    g1 ty in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u',
                                                                    ty_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_univ
                                                                    u u'
                                                                    then
                                                                    let uu___17
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (126)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun x ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Pulse_Typing.T_ElimExists
                                                                    (g1, u,
                                                                    ty, p, x,
                                                                    (), ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (126)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun d ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g1
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Ghost)
                                                                    (Pulse_Syntax_Base.Tm_ElimExists
                                                                    {
                                                                    Pulse_Syntax_Base.p4
                                                                    =
                                                                    (Pulse_Syntax_Pure.tm_exists_sl
                                                                    u
                                                                    (Pulse_Syntax_Base.as_binder
                                                                    ty) p)
                                                                    }))
                                                                    (Pulse_Typing.comp_elim_exists
                                                                    u ty p
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    x)) d
                                                                    post_hint in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (110)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    false g
                                                                    pre ()
                                                                    uu___21
                                                                    res_ppname))
                                                                    uu___21) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (110)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (126)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g pre
                                                                    uu___20
                                                                    post_hint
                                                                    t_rng))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___18))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    t_rng)
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_elim_exists: universe checking failed, computed "
                                                                    (Prims.strcat
                                                                    (Pulse_Syntax_Printer.univ_to_string
                                                                    u')
                                                                    ", expected "))
                                                                    (Prims.strcat
                                                                    (Pulse_Syntax_Printer.univ_to_string
                                                                    u) ""))))
                                                                    uu___16)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___7)))
                                                          uu___5))) uu___4)))
                                uu___2))) uu___1)
let (intro_exists_witness_singleton :
  Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.p5 = uu___;
          Pulse_Syntax_Base.witnesses = uu___1::[];_}
        -> true
    | uu___ -> false
let (intro_exists_slprop :
  Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.slprop) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.p5 = p; Pulse_Syntax_Base.witnesses = uu___;_} ->
        p
let (check_intro_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              unit FStar_Pervasives_Native.option ->
                ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun st ->
              fun slprop_typing ->
                let uu___ =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          Pulse_Typing_Env.push_context g
                            "check_intro_exists_non_erased"
                            st.Pulse_Syntax_Base.range1)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
                           (Prims.of_int (108)) (Prims.of_int (10))
                           (Prims.of_int (108)) (Prims.of_int (82)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Exists.fst"
                           (Prims.of_int (108)) (Prims.of_int (85))
                           (Prims.of_int (133)) (Prims.of_int (54)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun g1 ->
                        let uu___1 =
                          Obj.magic
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 -> st.Pulse_Syntax_Base.term1)) in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Exists.fst"
                                      (Prims.of_int (110))
                                      (Prims.of_int (52))
                                      (Prims.of_int (110))
                                      (Prims.of_int (59)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Exists.fst"
                                      (Prims.of_int (108))
                                      (Prims.of_int (85))
                                      (Prims.of_int (133))
                                      (Prims.of_int (54)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   match uu___2 with
                                   | Pulse_Syntax_Base.Tm_IntroExists
                                       { Pulse_Syntax_Base.p5 = t;
                                         Pulse_Syntax_Base.witnesses =
                                           witness::[];_}
                                       ->
                                       let uu___3 =
                                         match slprop_typing with
                                         | FStar_Pervasives_Native.Some
                                             typing ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        Prims.Mkdtuple2
                                                          (t, ()))))
                                         | uu___4 ->
                                             Obj.magic
                                               (Obj.repr
                                                  (Pulse_Checker_Pure.check_slprop
                                                     g1 t)) in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Exists.fst"
                                                     (Prims.of_int (112))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (114))
                                                     (Prims.of_int (27)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Exists.fst"
                                                     (Prims.of_int (110))
                                                     (Prims.of_int (62))
                                                     (Prims.of_int (133))
                                                     (Prims.of_int (54)))))
                                            (Obj.magic uu___3)
                                            (fun uu___4 ->
                                               (fun uu___4 ->
                                                  match uu___4 with
                                                  | Prims.Mkdtuple2
                                                      (t1, t_typing) ->
                                                      let uu___5 =
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___6 ->
                                                                Pulse_Syntax_Pure.inspect_term
                                                                  t1)) in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (25)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (54)))))
                                                           (Obj.magic uu___5)
                                                           (fun uu___6 ->
                                                              (fun tv ->
                                                                 let uu___6 =
                                                                   if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Pure.uu___is_Tm_ExistsSL
                                                                    tv)
                                                                   then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    t1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "check_intro_exists_non_erased: slprop "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    " is not an existential"))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.range1))
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
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    tv)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Pure.Tm_ExistsSL
                                                                    (u, b, p)
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing_Metatheory_Base.tm_exists_inversion
                                                                    g1 u
                                                                    b.Pulse_Syntax_Base.binder_ty
                                                                    p ()
                                                                    (Pulse_Typing_Env.fresh
                                                                    g1))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (ty_typing,
                                                                    uu___12)
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Pulse_Checker_Pure.check_term
                                                                    g1
                                                                    witness
                                                                    FStar_TypeChecker_Core.E_Ghost
                                                                    b.Pulse_Syntax_Base.binder_ty in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (witness1,
                                                                    witness_typing)
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Pulse_Typing.T_IntroExists
                                                                    (g1, u,
                                                                    b, p,
                                                                    witness1,
                                                                    (), (),
                                                                    ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun d ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Typing.comp_intro_exists
                                                                    u b p
                                                                    witness1),
                                                                    d))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (54)))))
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
                                                                    (c, d1)
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
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (54)))))
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
                                                                    let uu___21
                                                                    =
                                                                    Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g1
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Ghost)
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.p5
                                                                    =
                                                                    (Pulse_Syntax_Pure.tm_exists_sl
                                                                    u b p);
                                                                    Pulse_Syntax_Base.witnesses
                                                                    =
                                                                    [witness1]
                                                                    })) c d1
                                                                    post_hint in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    false g
                                                                    pre ()
                                                                    uu___22
                                                                    res_ppname))
                                                                    uu___22) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Exists.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g pre
                                                                    uu___21
                                                                    post_hint
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t1)))
                                                                    uu___21)))
                                                                    uu___19)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___14)))
                                                                    uu___11)))
                                                                    uu___9)))
                                                                    uu___7)))
                                                                uu___6)))
                                                 uu___4))) uu___2))) uu___1)