open Prims
let (check_prop :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, unit) Prims.dtuple2, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                 (Prims.of_int (14)) (Prims.of_int (11)) (Prims.of_int (14))
                 (Prims.of_int (12)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                 (Prims.of_int (14)) (Prims.of_int (15)) (Prims.of_int (25))
                 (Prims.of_int (30)))))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> p))
        (fun uu___ ->
           (fun p0 ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                            (Prims.of_int (15)) (Prims.of_int (26))
                            (Prims.of_int (15)) (Prims.of_int (70)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                            (Prims.of_int (14)) (Prims.of_int (15))
                            (Prims.of_int (25)) (Prims.of_int (30)))))
                   (Obj.magic
                      (Pulse_Checker_Pure.check_vprop g
                         (Pulse_Syntax_Base.tm_pure p)))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | Prims.Mkdtuple2 (p1, p_typing) ->
                             (match p1.Pulse_Syntax_Base.t with
                              | Pulse_Syntax_Base.Tm_Pure pp ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             Prims.Mkdtuple2 (pp, ()))))
                              | uu___1 ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.IntroPure.fst"
                                                   (Prims.of_int (22))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (30)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.IntroPure.fst"
                                                   (Prims.of_int (21))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (30)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.IntroPure.fst"
                                                         (Prims.of_int (25))
                                                         (Prims.of_int (9))
                                                         (Prims.of_int (25))
                                                         (Prims.of_int (29)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.IntroPure.fst"
                                                         (Prims.of_int (22))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (25))
                                                         (Prims.of_int (30)))))
                                                (Obj.magic
                                                   (Pulse_Syntax_Printer.term_to_string
                                                      p1))
                                                (fun uu___2 ->
                                                   (fun uu___2 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (30)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (30)))))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (40)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                 (Obj.magic
                                                                    (
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Base.tm_pure
                                                                    p0)))
                                                                 (fun uu___3
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Impossible: check_intro_pure: checking a pure vprop "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " returned a non-pure vprop "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ",please file a bug-report")))))
                                                           (fun uu___3 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   uu___3
                                                                    uu___2))))
                                                     uu___2)))
                                          (fun uu___2 ->
                                             (fun uu___2 ->
                                                Obj.magic
                                                  (Pulse_Typing_Env.fail g
                                                     FStar_Pervasives_Native.None
                                                     uu___2)) uu___2)))))
                        uu___))) uu___)
let (check_prop_validity :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        ((unit, unit) Pulse_Typing.prop_validity, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p -> fun typing -> Pulse_Checker_Pure.check_prop_validity g p ()
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.st_term ->
            ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun t ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                       (Prims.of_int (39)) (Prims.of_int (10))
                       (Prims.of_int (39)) (Prims.of_int (68)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                       (Prims.of_int (39)) (Prims.of_int (71))
                       (Prims.of_int (45)) (Prims.of_int (72)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Pulse_Typing_Env.push_context g "check_intro_pure"
                      t.Pulse_Syntax_Base.range2))
              (fun uu___ ->
                 (fun g1 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.IntroPure.fst"
                                  (Prims.of_int (41)) (Prims.of_int (27))
                                  (Prims.of_int (41)) (Prims.of_int (33)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.IntroPure.fst"
                                  (Prims.of_int (39)) (Prims.of_int (71))
                                  (Prims.of_int (45)) (Prims.of_int (72)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> t.Pulse_Syntax_Base.term1))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | Pulse_Syntax_Base.Tm_IntroPure
                                   { Pulse_Syntax_Base.p = p;_} ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.IntroPure.fst"
                                                 (Prims.of_int (42))
                                                 (Prims.of_int (26))
                                                 (Prims.of_int (42))
                                                 (Prims.of_int (40)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.IntroPure.fst"
                                                 (Prims.of_int (41))
                                                 (Prims.of_int (36))
                                                 (Prims.of_int (45))
                                                 (Prims.of_int (72)))))
                                        (Obj.magic (check_prop g1 p))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | Prims.Mkdtuple2
                                                  (p1, p_typing) ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.IntroPure.fst"
                                                                (Prims.of_int (43))
                                                                (Prims.of_int (11))
                                                                (Prims.of_int (43))
                                                                (Prims.of_int (43)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.IntroPure.fst"
                                                                (Prims.of_int (43))
                                                                (Prims.of_int (46))
                                                                (Prims.of_int (45))
                                                                (Prims.of_int (72)))))
                                                       (Obj.magic
                                                          (check_prop_validity
                                                             g1 p1 ()))
                                                       (fun uu___2 ->
                                                          (fun pv ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (45)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (72)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing.T_IntroPure
                                                                    (g1, p1,
                                                                    (), pv)))
                                                                  (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    st_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (72)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    g pre ()
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_IntroPure
                                                                    {
                                                                    Pulse_Syntax_Base.p
                                                                    = p1
                                                                    }))
                                                                    (Pulse_Typing.comp_intro_pure
                                                                    p1)
                                                                    st_typing))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g pre
                                                                    uu___2
                                                                    post_hint
                                                                    t.Pulse_Syntax_Base.range2))
                                                                    uu___2)))
                                                                    uu___2)))
                                                            uu___2))) uu___1)))
                              uu___))) uu___)