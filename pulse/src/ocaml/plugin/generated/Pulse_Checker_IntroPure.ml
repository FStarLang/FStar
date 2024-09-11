open Prims
let (check_prop :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, unit) Prims.dtuple2, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      let uu___ =
        Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> p)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                 (Prims.of_int (30)) (Prims.of_int (11)) (Prims.of_int (30))
                 (Prims.of_int (12)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                 (Prims.of_int (30)) (Prims.of_int (15)) (Prims.of_int (41))
                 (Prims.of_int (30))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun p0 ->
              let uu___1 =
                Pulse_Checker_Pure.check_slprop g
                  (Pulse_Syntax_Pure.tm_pure p) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                            (Prims.of_int (31)) (Prims.of_int (26))
                            (Prims.of_int (31)) (Prims.of_int (71)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                            (Prims.of_int (30)) (Prims.of_int (15))
                            (Prims.of_int (41)) (Prims.of_int (30)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 ->
                         match uu___2 with
                         | Prims.Mkdtuple2 (p1, p_typing) ->
                             (match Pulse_Syntax_Pure.inspect_term p1 with
                              | Pulse_Syntax_Pure.Tm_Pure pp ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 ->
                                             Prims.Mkdtuple2 (pp, ()))))
                              | uu___3 ->
                                  Obj.magic
                                    (Obj.repr
                                       (let uu___4 =
                                          let uu___5 =
                                            Pulse_Syntax_Printer.term_to_string
                                              p1 in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.IntroPure.fst"
                                                     (Prims.of_int (41))
                                                     (Prims.of_int (9))
                                                     (Prims.of_int (41))
                                                     (Prims.of_int (29)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.IntroPure.fst"
                                                     (Prims.of_int (38))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (41))
                                                     (Prims.of_int (30)))))
                                            (Obj.magic uu___5)
                                            (fun uu___6 ->
                                               (fun uu___6 ->
                                                  let uu___7 =
                                                    let uu___8 =
                                                      Pulse_Syntax_Printer.term_to_string
                                                        (Pulse_Syntax_Pure.tm_pure
                                                           p0) in
                                                    FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.IntroPure.fst"
                                                               (Prims.of_int (40))
                                                               (Prims.of_int (9))
                                                               (Prims.of_int (40))
                                                               (Prims.of_int (40)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Printf.fst"
                                                               (Prims.of_int (122))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (124))
                                                               (Prims.of_int (44)))))
                                                      (Obj.magic uu___8)
                                                      (fun uu___9 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___10 ->
                                                              fun x ->
                                                                Prims.strcat
                                                                  (Prims.strcat
                                                                    "Impossible: check_intro_pure: checking a pure slprop "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    " returned a non-pure slprop "))
                                                                  (Prims.strcat
                                                                    x
                                                                    ",please file a bug-report"))) in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.IntroPure.fst"
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (41))
                                                                (Prims.of_int (30)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.IntroPure.fst"
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (41))
                                                                (Prims.of_int (30)))))
                                                       (Obj.magic uu___7)
                                                       (fun uu___8 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___9 ->
                                                               uu___8 uu___6))))
                                                 uu___6) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.IntroPure.fst"
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (41))
                                                   (Prims.of_int (30)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.IntroPure.fst"
                                                   (Prims.of_int (37))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (41))
                                                   (Prims.of_int (30)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             (fun uu___5 ->
                                                Obj.magic
                                                  (Pulse_Typing_Env.fail g
                                                     FStar_Pervasives_Native.None
                                                     uu___5)) uu___5)))))
                        uu___2))) uu___1)
let (check_prop_validity :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p -> fun typing -> Pulse_Checker_Pure.check_prop_validity g p ()
let (check :
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
                        Pulse_Typing_Env.push_context g "check_intro_pure"
                          t.Pulse_Syntax_Base.range1)) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                         (Prims.of_int (56)) (Prims.of_int (10))
                         (Prims.of_int (56)) (Prims.of_int (68)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                         (Prims.of_int (56)) (Prims.of_int (71))
                         (Prims.of_int (62)) (Prims.of_int (131)))))
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
                                    "Pulse.Checker.IntroPure.fst"
                                    (Prims.of_int (58)) (Prims.of_int (27))
                                    (Prims.of_int (58)) (Prims.of_int (33)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.IntroPure.fst"
                                    (Prims.of_int (56)) (Prims.of_int (71))
                                    (Prims.of_int (62)) (Prims.of_int (131)))))
                           (Obj.magic uu___1)
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 match uu___2 with
                                 | Pulse_Syntax_Base.Tm_IntroPure
                                     { Pulse_Syntax_Base.p3 = p;_} ->
                                     let uu___3 = check_prop g1 p in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.IntroPure.fst"
                                                   (Prims.of_int (59))
                                                   (Prims.of_int (26))
                                                   (Prims.of_int (59))
                                                   (Prims.of_int (40)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.IntroPure.fst"
                                                   (Prims.of_int (58))
                                                   (Prims.of_int (36))
                                                   (Prims.of_int (62))
                                                   (Prims.of_int (131)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             (fun uu___4 ->
                                                match uu___4 with
                                                | Prims.Mkdtuple2
                                                    (p1, p_typing) ->
                                                    let uu___5 =
                                                      check_prop_validity g1
                                                        p1 () in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.IntroPure.fst"
                                                                  (Prims.of_int (60))
                                                                  (Prims.of_int (11))
                                                                  (Prims.of_int (60))
                                                                  (Prims.of_int (43)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.IntroPure.fst"
                                                                  (Prims.of_int (60))
                                                                  (Prims.of_int (46))
                                                                  (Prims.of_int (62))
                                                                  (Prims.of_int (131)))))
                                                         (Obj.magic uu___5)
                                                         (fun uu___6 ->
                                                            (fun pv ->
                                                               let uu___6 =
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing.T_IntroPure
                                                                    (g1, p1,
                                                                    (), ()))) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (45)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (131)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___6)
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    st_typing
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g1
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Ghost)
                                                                    (Pulse_Syntax_Base.Tm_IntroPure
                                                                    {
                                                                    Pulse_Syntax_Base.p3
                                                                    = p1
                                                                    }))
                                                                    (Pulse_Typing.comp_intro_pure
                                                                    p1)
                                                                    st_typing
                                                                    post_hint in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (113)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    false g
                                                                    pre ()
                                                                    uu___9
                                                                    res_ppname))
                                                                    uu___9) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (113)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (131)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g pre
                                                                    uu___8
                                                                    post_hint
                                                                    t.Pulse_Syntax_Base.range1))
                                                                    uu___8)))
                                                                    uu___7)))
                                                              uu___6)))
                                               uu___4))) uu___2))) uu___1)