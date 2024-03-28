open Prims
let (push_context :
  Prims.string ->
    Pulse_Syntax_Base.range -> Pulse_Typing_Env.env -> Pulse_Typing_Env.env)
  = fun ctx -> fun r -> fun g -> Pulse_Typing_Env.push_context g ctx r
let (debug :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun msg ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (37)) (Prims.of_int (22)) (Prims.of_int (37))
                 (Prims.of_int (36)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (38)) (Prims.of_int (2)) (Prims.of_int (39))
                 (Prims.of_int (47)))))
        (Obj.magic (FStar_Tactics_V2_Builtins.debugging ()))
        (fun uu___ ->
           (fun tac_debugging ->
              if
                tac_debugging ||
                  (Pulse_RuntimeUtils.debug_at_level
                     (Pulse_Typing_Env.fstar_env g) "refl_tc_callbacks")
              then
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (39)) (Prims.of_int (15))
                                 (Prims.of_int (39)) (Prims.of_int (47)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (39)) (Prims.of_int (7))
                                 (Prims.of_int (39)) (Prims.of_int (47)))))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (39))
                                       (Prims.of_int (16))
                                       (Prims.of_int (39))
                                       (Prims.of_int (31)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (39))
                                       (Prims.of_int (15))
                                       (Prims.of_int (39))
                                       (Prims.of_int (47)))))
                              (Obj.magic (Pulse_Typing_Env.print_context g))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (39))
                                                  (Prims.of_int (34))
                                                  (Prims.of_int (39))
                                                  (Prims.of_int (46)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "prims.fst"
                                                  (Prims.of_int (590))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (590))
                                                  (Prims.of_int (31)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (39))
                                                        (Prims.of_int (41))
                                                        (Prims.of_int (39))
                                                        (Prims.of_int (46)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (590))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (590))
                                                        (Prims.of_int (31)))))
                                               (Obj.magic (msg ()))
                                               (fun uu___1 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       Prims.strcat "\n"
                                                         uu___1))))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 Prims.strcat uu___ uu___1))))
                                   uu___)))
                        (fun uu___ ->
                           (fun uu___ ->
                              Obj.magic
                                (FStar_Tactics_V2_Builtins.print uu___))
                             uu___)))
              else
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
             uu___)
let (check_ln :
  Pulse_Typing_Env.env ->
    Prims.string ->
      FStar_Reflection_Types.term ->
        (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun label ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (42)) (Prims.of_int (5)) (Prims.of_int (42))
                   (Prims.of_int (29)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (42)) (Prims.of_int (2)) (Prims.of_int (47))
                   (Prims.of_int (5)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (42)) (Prims.of_int (9))
                         (Prims.of_int (42)) (Prims.of_int (29)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (42)) (Prims.of_int (5))
                         (Prims.of_int (42)) (Prims.of_int (29)))))
                (Obj.magic (FStar_Tactics_CheckLN.check_ln t))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 -> Prims.op_Negation uu___))))
          (fun uu___ ->
             (fun uu___ ->
                if uu___
                then
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (43)) (Prims.of_int (43))
                                   (Prims.of_int (47)) (Prims.of_int (5)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (43)) (Prims.of_int (4))
                                   (Prims.of_int (47)) (Prims.of_int (5)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (43))
                                         (Prims.of_int (43))
                                         (Prims.of_int (47))
                                         (Prims.of_int (5)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (43))
                                         (Prims.of_int (43))
                                         (Prims.of_int (47))
                                         (Prims.of_int (5)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (45))
                                               (Prims.of_int (6))
                                               (Prims.of_int (45))
                                               (Prims.of_int (49)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (43))
                                               (Prims.of_int (43))
                                               (Prims.of_int (47))
                                               (Prims.of_int (5)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Pure.fst"
                                                     (Prims.of_int (45))
                                                     (Prims.of_int (41))
                                                     (Prims.of_int (45))
                                                     (Prims.of_int (49)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Pure.fst"
                                                     (Prims.of_int (45))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (45))
                                                     (Prims.of_int (49)))))
                                            (Obj.magic
                                               (Pulse_PP.pp
                                                  Pulse_PP.printable_string
                                                  label))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                      (Pulse_PP.text
                                                         "Aborting before calling")
                                                      uu___1))))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (43))
                                                          (Prims.of_int (43))
                                                          (Prims.of_int (47))
                                                          (Prims.of_int (5)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (43))
                                                          (Prims.of_int (43))
                                                          (Prims.of_int (47))
                                                          (Prims.of_int (5)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Pure.fst"
                                                                (Prims.of_int (46))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (46))
                                                                (Prims.of_int (37)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Pure.fst"
                                                                (Prims.of_int (43))
                                                                (Prims.of_int (43))
                                                                (Prims.of_int (47))
                                                                (Prims.of_int (5)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (37)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (37)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (37)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (37)))))
                                                                   (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    t))
                                                                   (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.equals
                                                                    uu___2))))
                                                             (fun uu___2 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___3
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "term")
                                                                    uu___2))))
                                                       (fun uu___2 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___3 ->
                                                               [uu___2]))))
                                                 (fun uu___2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 -> uu___1
                                                         :: uu___2)))) uu___1)))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        (Pulse_PP.text
                                           "Failure: not locally nameless!")
                                        :: uu___1))))
                          (fun uu___1 ->
                             (fun uu___1 ->
                                Obj.magic
                                  (Pulse_Typing_Env.fail_doc g
                                     (FStar_Pervasives_Native.Some
                                        (Pulse_RuntimeUtils.range_of_term t))
                                     uu___1)) uu___1)))
                else
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
               uu___)
let (rtb_core_compute_term_type :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((FStar_TypeChecker_Core.tot_or_ghost * FStar_Reflection_Types.typ)
           FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (50)) (Prims.of_int (2)) (Prims.of_int (50))
                   (Prims.of_int (38)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (51)) (Prims.of_int (2)) (Prims.of_int (56))
                   (Prims.of_int (5)))))
          (Obj.magic (check_ln g "rtb_compute_term_type" e))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (51)) (Prims.of_int (2))
                              (Prims.of_int (54)) (Prims.of_int (31)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (54)) (Prims.of_int (32))
                              (Prims.of_int (56)) (Prims.of_int (5)))))
                     (Obj.magic
                        (debug g
                           (fun uu___1 ->
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (54))
                                         (Prims.of_int (10))
                                         (Prims.of_int (54))
                                         (Prims.of_int (30)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (52))
                                         (Prims.of_int (4))
                                         (Prims.of_int (54))
                                         (Prims.of_int (30)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Builtins.term_to_string
                                      e))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (52))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (54))
                                                    (Prims.of_int (30)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (52))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (54))
                                                    (Prims.of_int (30)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (53))
                                                          (Prims.of_int (10))
                                                          (Prims.of_int (53))
                                                          (Prims.of_int (50)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Printf.fst"
                                                          (Prims.of_int (122))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (124))
                                                          (Prims.of_int (44)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_V2_Builtins.range_to_string
                                                       (Pulse_RuntimeUtils.range_of_term
                                                          e)))
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 ->
                                                         fun x ->
                                                           Prims.strcat
                                                             (Prims.strcat
                                                                "("
                                                                (Prims.strcat
                                                                   uu___3
                                                                   ") Calling core_check_term on "))
                                                             (Prims.strcat x
                                                                "")))))
                                           (fun uu___3 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___4 -> uu___3 uu___2))))
                                     uu___2))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (55))
                                         (Prims.of_int (12))
                                         (Prims.of_int (55))
                                         (Prims.of_int (85)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (55))
                                         (Prims.of_int (6))
                                         (Prims.of_int (55))
                                         (Prims.of_int (9)))))
                                (Obj.magic
                                   (Pulse_RuntimeUtils.with_context
                                      (Pulse_Typing_Env.get_context g)
                                      (fun uu___2 ->
                                         FStar_Tactics_V2_Builtins.core_compute_term_type
                                           f e)))
                                (fun res ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> res)))) uu___1))) uu___)
let (rtb_tc_term :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((FStar_Reflection_Types.term * (FStar_TypeChecker_Core.tot_or_ghost
           * FStar_Reflection_Types.typ)) FStar_Pervasives_Native.option *
           FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (60)) (Prims.of_int (2)) (Prims.of_int (60))
                   (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (60)) (Prims.of_int (29))
                   (Prims.of_int (67)) (Prims.of_int (5)))))
          (Obj.magic (check_ln g "rtb_tc_term" e))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (61)) (Prims.of_int (10))
                              (Prims.of_int (61)) (Prims.of_int (51)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (62)) (Prims.of_int (2))
                              (Prims.of_int (67)) (Prims.of_int (5)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           Pulse_RuntimeUtils.deep_transform_to_unary_applications
                             e))
                     (fun uu___1 ->
                        (fun e1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (62))
                                         (Prims.of_int (2))
                                         (Prims.of_int (65))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (65))
                                         (Prims.of_int (28))
                                         (Prims.of_int (67))
                                         (Prims.of_int (5)))))
                                (Obj.magic
                                   (debug g
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (65))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (65))
                                                    (Prims.of_int (26)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (63))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (65))
                                                    (Prims.of_int (26)))))
                                           (Obj.magic
                                              (FStar_Tactics_V2_Builtins.term_to_string
                                                 e1))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (63))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (65))
                                                               (Prims.of_int (26)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (63))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (65))
                                                               (Prims.of_int (26)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (46)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_V2_Builtins.range_to_string
                                                                  (Pulse_RuntimeUtils.range_of_term
                                                                    e1)))
                                                            (fun uu___3 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___4
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "("
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    ") Calling tc_term on "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              uu___3 uu___2))))
                                                uu___2))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (66))
                                                    (Prims.of_int (12))
                                                    (Prims.of_int (66))
                                                    (Prims.of_int (70)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (66))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (66))
                                                    (Prims.of_int (9)))))
                                           (Obj.magic
                                              (Pulse_RuntimeUtils.with_context
                                                 (Pulse_Typing_Env.get_context
                                                    g)
                                                 (fun uu___2 ->
                                                    FStar_Tactics_V2_Builtins.tc_term
                                                      f e1)))
                                           (fun res ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 -> res)))) uu___1)))
                          uu___1))) uu___)
let (rtb_universe_of :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        ((FStar_Reflection_Types.universe FStar_Pervasives_Native.option *
           FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (70)) (Prims.of_int (2)) (Prims.of_int (70))
                   (Prims.of_int (32)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (71)) (Prims.of_int (2)) (Prims.of_int (76))
                   (Prims.of_int (5)))))
          (Obj.magic (check_ln g "rtb_universe_of" e))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (71)) (Prims.of_int (2))
                              (Prims.of_int (74)) (Prims.of_int (27)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (74)) (Prims.of_int (28))
                              (Prims.of_int (76)) (Prims.of_int (5)))))
                     (Obj.magic
                        (debug g
                           (fun uu___1 ->
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (74))
                                         (Prims.of_int (6))
                                         (Prims.of_int (74))
                                         (Prims.of_int (26)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (72))
                                         (Prims.of_int (4))
                                         (Prims.of_int (74))
                                         (Prims.of_int (26)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Builtins.term_to_string
                                      e))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (72))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (74))
                                                    (Prims.of_int (26)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (72))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (74))
                                                    (Prims.of_int (26)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (73))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (73))
                                                          (Prims.of_int (46)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Printf.fst"
                                                          (Prims.of_int (122))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (124))
                                                          (Prims.of_int (44)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_V2_Builtins.range_to_string
                                                       (Pulse_RuntimeUtils.range_of_term
                                                          e)))
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 ->
                                                         fun x ->
                                                           Prims.strcat
                                                             (Prims.strcat
                                                                "("
                                                                (Prims.strcat
                                                                   uu___3
                                                                   ") Calling universe_of on "))
                                                             (Prims.strcat x
                                                                "")))))
                                           (fun uu___3 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___4 -> uu___3 uu___2))))
                                     uu___2))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (75))
                                         (Prims.of_int (12))
                                         (Prims.of_int (75))
                                         (Prims.of_int (74)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (75))
                                         (Prims.of_int (6))
                                         (Prims.of_int (75))
                                         (Prims.of_int (9)))))
                                (Obj.magic
                                   (Pulse_RuntimeUtils.with_context
                                      (Pulse_Typing_Env.get_context g)
                                      (fun uu___2 ->
                                         FStar_Tactics_V2_Builtins.universe_of
                                           f e)))
                                (fun res ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> res)))) uu___1))) uu___)
let (rtb_check_subtyping :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (((unit, unit, unit) Pulse_Typing.subtyping_token
           FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (79)) (Prims.of_int (11))
                   (Prims.of_int (79)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (79)) (Prims.of_int (26))
                   (Prims.of_int (90)) (Prims.of_int (5)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Elaborate_Pure.elab_term t1))
          (fun uu___ ->
             (fun e1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (80)) (Prims.of_int (11))
                              (Prims.of_int (80)) (Prims.of_int (23)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (81)) (Prims.of_int (2))
                              (Prims.of_int (90)) (Prims.of_int (5)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Pulse_Elaborate_Pure.elab_term t2))
                     (fun uu___ ->
                        (fun e2 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (81))
                                         (Prims.of_int (2))
                                         (Prims.of_int (81))
                                         (Prims.of_int (40)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (82))
                                         (Prims.of_int (2))
                                         (Prims.of_int (90))
                                         (Prims.of_int (5)))))
                                (Obj.magic
                                   (check_ln g "rtb_check_subtyping.t1" e1))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (82))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (82))
                                                    (Prims.of_int (40)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (83))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (90))
                                                    (Prims.of_int (5)))))
                                           (Obj.magic
                                              (check_ln g
                                                 "rtb_check_subtyping.t2" e2))
                                           (fun uu___1 ->
                                              (fun uu___1 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (83))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (88))
                                                               (Prims.of_int (30)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (88))
                                                               (Prims.of_int (31))
                                                               (Prims.of_int (90))
                                                               (Prims.of_int (5)))))
                                                      (Obj.magic
                                                         (debug g
                                                            (fun uu___2 ->
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                 (Obj.magic
                                                                    (
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    t2))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    t1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.range_to_string
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t2)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.range_to_string
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t1)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "("
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    ", "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ") Calling check_subtyping on "))
                                                                    (Prims.strcat
                                                                    x1 " <: "))
                                                                    (Prims.strcat
                                                                    x2 "")))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6
                                                                    uu___5))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    uu___4))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                    uu___3))))
                                                      (fun uu___2 ->
                                                         (fun uu___2 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (93)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (9)))))
                                                                 (Obj.magic
                                                                    (
                                                                    Pulse_RuntimeUtils.with_context
                                                                    (Pulse_Typing_Env.get_context
                                                                    g)
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_V2_Builtins.check_subtyping
                                                                    (Pulse_Typing.elab_env
                                                                    g) e1 e2)))
                                                                 (fun res ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    res))))
                                                           uu___2))) uu___1)))
                                     uu___))) uu___))) uu___)
let (rtb_instantiate_implicits :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        ((((FStar_Reflection_Types.namedv * FStar_Reflection_Types.typ)
           Prims.list * FStar_Reflection_Types.term *
           FStar_Reflection_Types.typ) FStar_Pervasives_Native.option *
           FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (93)) (Prims.of_int (2)) (Prims.of_int (93))
                   (Prims.of_int (42)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (94)) (Prims.of_int (2))
                   (Prims.of_int (105)) (Prims.of_int (12)))))
          (Obj.magic (check_ln g "rtb_instantiate_implicits" t))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (94)) (Prims.of_int (2))
                              (Prims.of_int (95)) (Prims.of_int (60)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (95)) (Prims.of_int (61))
                              (Prims.of_int (105)) (Prims.of_int (12)))))
                     (Obj.magic
                        (debug g
                           (fun uu___1 ->
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (95))
                                         (Prims.of_int (39))
                                         (Prims.of_int (95))
                                         (Prims.of_int (59)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "prims.fst"
                                         (Prims.of_int (590))
                                         (Prims.of_int (19))
                                         (Prims.of_int (590))
                                         (Prims.of_int (31)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Builtins.term_to_string
                                      t))
                                (fun uu___2 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 ->
                                        Prims.strcat
                                          "Calling instantiate_implicits on "
                                          (Prims.strcat uu___2 ""))))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (97))
                                         (Prims.of_int (10))
                                         (Prims.of_int (97))
                                         (Prims.of_int (51)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (97))
                                         (Prims.of_int (54))
                                         (Prims.of_int (105))
                                         (Prims.of_int (12)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      Pulse_RuntimeUtils.deep_transform_to_unary_applications
                                        t))
                                (fun uu___2 ->
                                   (fun t1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (98))
                                                    (Prims.of_int (17))
                                                    (Prims.of_int (98))
                                                    (Prims.of_int (89)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (97))
                                                    (Prims.of_int (54))
                                                    (Prims.of_int (105))
                                                    (Prims.of_int (12)))))
                                           (Obj.magic
                                              (Pulse_RuntimeUtils.with_context
                                                 (Pulse_Typing_Env.get_context
                                                    g)
                                                 (fun uu___2 ->
                                                    FStar_Tactics_V2_Builtins.instantiate_implicits
                                                      f t1)))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 match uu___2 with
                                                 | (res, iss) ->
                                                     (match res with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (66)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (12)))))
                                                               (Obj.magic
                                                                  (debug g
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    "Returned from instantiate_implicits: None")))
                                                                    uu___3)))
                                                               (fun uu___3 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    (res,
                                                                    iss))))
                                                      | FStar_Pervasives_Native.Some
                                                          (uu___3, t2,
                                                           uu___4)
                                                          ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (100)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (12)))))
                                                               (Obj.magic
                                                                  (debug g
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    t2))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "Returned from instantiate_implicits: "
                                                                    (Prims.strcat
                                                                    uu___6 ""))))))
                                                               (fun uu___5 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___6 ->
                                                                    (res,
                                                                    iss))))))
                                                uu___2))) uu___2))) uu___1)))
               uu___)
let (rtb_core_check_term :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        FStar_TypeChecker_Core.tot_or_ghost ->
          FStar_Reflection_Types.term ->
            (((unit, unit, unit) FStar_Tactics_Types.typing_token
               FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        fun eff ->
          fun t ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (108)) (Prims.of_int (2))
                       (Prims.of_int (108)) (Prims.of_int (38)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (109)) (Prims.of_int (2))
                       (Prims.of_int (116)) (Prims.of_int (5)))))
              (Obj.magic (check_ln g "rtb_core_check_term.e" e))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (109)) (Prims.of_int (2))
                                  (Prims.of_int (109)) (Prims.of_int (38)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (110)) (Prims.of_int (2))
                                  (Prims.of_int (116)) (Prims.of_int (5)))))
                         (Obj.magic (check_ln g "rtb_core_check_term.t" t))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (110))
                                             (Prims.of_int (2))
                                             (Prims.of_int (114))
                                             (Prims.of_int (37)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (114))
                                             (Prims.of_int (38))
                                             (Prims.of_int (116))
                                             (Prims.of_int (5)))))
                                    (Obj.magic
                                       (debug g
                                          (fun uu___2 ->
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (114))
                                                        (Prims.of_int (16))
                                                        (Prims.of_int (114))
                                                        (Prims.of_int (36)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (111))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (114))
                                                        (Prims.of_int (36)))))
                                               (Obj.magic
                                                  (FStar_Tactics_V2_Builtins.term_to_string
                                                     t))
                                               (fun uu___3 ->
                                                  (fun uu___3 ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (111))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (114))
                                                                   (Prims.of_int (36)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (111))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (114))
                                                                   (Prims.of_int (36)))))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (36)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (36)))))
                                                                (Obj.magic
                                                                   (FStar_Tactics_V2_Builtins.term_to_string
                                                                    e))
                                                                (fun uu___4
                                                                   ->
                                                                   (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.range_to_string
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    e)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "("
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    ") Calling core_check_term on "))
                                                                    (Prims.strcat
                                                                    x " and "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    uu___4))))
                                                                    uu___4)))
                                                          (fun uu___4 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___5 ->
                                                                  uu___4
                                                                    uu___3))))
                                                    uu___3))))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (115))
                                                        (Prims.of_int (12))
                                                        (Prims.of_int (115))
                                                        (Prims.of_int (84)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (115))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (115))
                                                        (Prims.of_int (9)))))
                                               (Obj.magic
                                                  (Pulse_RuntimeUtils.with_context
                                                     (Pulse_Typing_Env.get_context
                                                        g)
                                                     (fun uu___3 ->
                                                        FStar_Tactics_V2_Builtins.core_check_term
                                                          f e t eff)))
                                               (fun res ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___3 -> res))))
                                         uu___2))) uu___1))) uu___)
let (rtb_core_check_term_at_type :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          ((FStar_TypeChecker_Core.tot_or_ghost
             FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        fun t ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (119)) (Prims.of_int (2))
                     (Prims.of_int (123)) (Prims.of_int (37)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (123)) (Prims.of_int (38))
                     (Prims.of_int (125)) (Prims.of_int (5)))))
            (Obj.magic
               (debug g
                  (fun uu___ ->
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (123)) (Prims.of_int (16))
                                (Prims.of_int (123)) (Prims.of_int (36)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (120)) (Prims.of_int (4))
                                (Prims.of_int (123)) (Prims.of_int (36)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Builtins.term_to_string t))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (120))
                                           (Prims.of_int (4))
                                           (Prims.of_int (123))
                                           (Prims.of_int (36)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (120))
                                           (Prims.of_int (4))
                                           (Prims.of_int (123))
                                           (Prims.of_int (36)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Pure.fst"
                                                 (Prims.of_int (122))
                                                 (Prims.of_int (16))
                                                 (Prims.of_int (122))
                                                 (Prims.of_int (36)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Pure.fst"
                                                 (Prims.of_int (120))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (123))
                                                 (Prims.of_int (36)))))
                                        (Obj.magic
                                           (FStar_Tactics_V2_Builtins.term_to_string
                                              e))
                                        (fun uu___2 ->
                                           (fun uu___2 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Pure.fst"
                                                            (Prims.of_int (120))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (123))
                                                            (Prims.of_int (36)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Pure.fst"
                                                            (Prims.of_int (120))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (123))
                                                            (Prims.of_int (36)))))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Pure.fst"
                                                                  (Prims.of_int (121))
                                                                  (Prims.of_int (16))
                                                                  (Prims.of_int (121))
                                                                  (Prims.of_int (56)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Printf.fst"
                                                                  (Prims.of_int (122))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (124))
                                                                  (Prims.of_int (44)))))
                                                         (Obj.magic
                                                            (FStar_Tactics_V2_Builtins.range_to_string
                                                               (Pulse_RuntimeUtils.range_of_term
                                                                  e)))
                                                         (fun uu___3 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___4 ->
                                                                 fun x ->
                                                                   fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "("
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    ") Calling core_check_term_at_type on "))
                                                                    (Prims.strcat
                                                                    x " and "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
                                                   (fun uu___3 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___4 ->
                                                           uu___3 uu___2))))
                                             uu___2)))
                                  (fun uu___2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 -> uu___2 uu___1))))
                            uu___1))))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (124)) (Prims.of_int (12))
                                (Prims.of_int (124)) (Prims.of_int (88)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (124)) (Prims.of_int (6))
                                (Prims.of_int (124)) (Prims.of_int (9)))))
                       (Obj.magic
                          (Pulse_RuntimeUtils.with_context
                             (Pulse_Typing_Env.get_context g)
                             (fun uu___1 ->
                                FStar_Tactics_V2_Builtins.core_check_term_at_type
                                  f e t)))
                       (fun res ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> res)))) uu___)
let (mk_squash0 : FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t ->
    let sq =
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_UInst
           ((FStar_Reflection_V2_Builtins.pack_fv
               FStar_Reflection_Const.squash_qn), [Pulse_Syntax_Pure.u_zero])) in
    FStar_Reflection_V2_Derived.mk_e_app sq [t]

let (rtb_check_prop_validity :
  Pulse_Typing_Env.env ->
    Prims.bool ->
      FStar_Reflection_Types.env ->
        FStar_Reflection_Types.term ->
          ((unit FStar_Pervasives_Native.option * FStar_Issue.issue
             Prims.list),
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun sync ->
      fun f ->
        fun p ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (136)) (Prims.of_int (2))
                     (Prims.of_int (136)) (Prims.of_int (40)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (137)) (Prims.of_int (2))
                     (Prims.of_int (151)) (Prims.of_int (65)))))
            (Obj.magic (check_ln g "rtb_check_prop_validity" p))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (137)) (Prims.of_int (2))
                                (Prims.of_int (140)) (Prims.of_int (31)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (140)) (Prims.of_int (32))
                                (Prims.of_int (151)) (Prims.of_int (65)))))
                       (Obj.magic
                          (debug g
                             (fun uu___1 ->
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (140))
                                           (Prims.of_int (10))
                                           (Prims.of_int (140))
                                           (Prims.of_int (30)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (138))
                                           (Prims.of_int (4))
                                           (Prims.of_int (140))
                                           (Prims.of_int (30)))))
                                  (Obj.magic
                                     (FStar_Tactics_V2_Builtins.term_to_string
                                        p))
                                  (fun uu___2 ->
                                     (fun uu___2 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (138))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (140))
                                                      (Prims.of_int (30)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (138))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (140))
                                                      (Prims.of_int (30)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Pure.fst"
                                                            (Prims.of_int (139))
                                                            (Prims.of_int (10))
                                                            (Prims.of_int (139))
                                                            (Prims.of_int (50)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Printf.fst"
                                                            (Prims.of_int (122))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (124))
                                                            (Prims.of_int (44)))))
                                                   (Obj.magic
                                                      (FStar_Tactics_V2_Builtins.range_to_string
                                                         (Pulse_RuntimeUtils.range_of_term
                                                            p)))
                                                   (fun uu___3 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___4 ->
                                                           fun x ->
                                                             Prims.strcat
                                                               (Prims.strcat
                                                                  "("
                                                                  (Prims.strcat
                                                                    uu___3
                                                                    ") Calling check_prop_validity on "))
                                                               (Prims.strcat
                                                                  x "")))))
                                             (fun uu___3 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___4 ->
                                                     uu___3 uu___2)))) uu___2))))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (141))
                                           (Prims.of_int (11))
                                           (Prims.of_int (141))
                                           (Prims.of_int (23)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (141))
                                           (Prims.of_int (26))
                                           (Prims.of_int (151))
                                           (Prims.of_int (65)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> mk_squash0 p))
                                  (fun uu___2 ->
                                     (fun sp ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (143))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (147))
                                                      (Prims.of_int (40)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (141))
                                                      (Prims.of_int (26))
                                                      (Prims.of_int (151))
                                                      (Prims.of_int (65)))))
                                             (Obj.magic
                                                (Pulse_RuntimeUtils.with_context
                                                   (Pulse_Typing_Env.get_context
                                                      g)
                                                   (fun uu___2 ->
                                                      if sync
                                                      then
                                                        FStar_Tactics_V2_Derived.with_policy
                                                          FStar_Tactics_Types.SMTSync
                                                          (fun uu___3 ->
                                                             FStar_Tactics_V2_Builtins.check_prop_validity
                                                               f sp)
                                                      else
                                                        FStar_Tactics_V2_Builtins.check_prop_validity
                                                          f sp)))
                                             (fun uu___2 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___3 ->
                                                     match uu___2 with
                                                     | (res, issues) ->
                                                         (match res with
                                                          | FStar_Pervasives_Native.None
                                                              ->
                                                              (FStar_Pervasives_Native.None,
                                                                issues)
                                                          | FStar_Pervasives_Native.Some
                                                              tok ->
                                                              ((FStar_Pervasives_Native.Some
                                                                  ()),
                                                                issues))))))
                                       uu___2))) uu___1))) uu___)
let (exn_as_issue : Prims.exn -> FStar_Issue.issue) =
  fun e ->
    FStar_Issue.mk_issue_doc "Error"
      [FStar_Pprint.arbitrary_string (Pulse_RuntimeUtils.print_exn e)]
      FStar_Pervasives_Native.None FStar_Pervasives_Native.None []
let catch_all :
  'a .
    (unit ->
       (('a FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
         unit) FStar_Tactics_Effect.tac_repr)
      ->
      (('a FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
        unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (158)) (Prims.of_int (10)) (Prims.of_int (158))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (158)) (Prims.of_int (4)) (Prims.of_int (161))
               (Prims.of_int (16)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.catch f))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | FStar_Pervasives.Inl exn ->
                  (FStar_Pervasives_Native.None, [exn_as_issue exn])
              | FStar_Pervasives.Inr v -> v))
let (readback_failure :
  FStar_Reflection_Types.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (165)) (Prims.of_int (17)) (Prims.of_int (165))
               (Prims.of_int (37)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (164)) (Prims.of_int (2)) (Prims.of_int (165))
               (Prims.of_int (37)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string s))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              Prims.strcat "Internal error: failed to readback F* term "
                (Prims.strcat uu___ "")))
let (ill_typed_term :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
        (FStar_Pprint.document Prims.list, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun expected_typ ->
      fun got_typ ->
        match (expected_typ, got_typ) with
        | (FStar_Pervasives_Native.None, uu___) ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (171)) (Prims.of_int (5))
                       (Prims.of_int (171)) (Prims.of_int (36)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (171)) (Prims.of_int (4))
                       (Prims.of_int (171)) (Prims.of_int (37)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (171)) (Prims.of_int (32))
                             (Prims.of_int (171)) (Prims.of_int (36)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (171)) (Prims.of_int (5))
                             (Prims.of_int (171)) (Prims.of_int (36)))))
                    (Obj.magic (Pulse_PP.pp Pulse_PP.printable_fstar_term t))
                    (fun uu___1 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___2 ->
                            FStar_Pprint.op_Hat_Hat
                              (Pulse_PP.text "Ill-typed term: ") uu___1))))
              (fun uu___1 ->
                 FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> [uu___1]))
        | (FStar_Pervasives_Native.Some ty, FStar_Pervasives_Native.None) ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (173)) (Prims.of_int (5))
                       (Prims.of_int (174)) (Prims.of_int (37)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (173)) (Prims.of_int (4))
                       (Prims.of_int (174)) (Prims.of_int (38)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (173)) (Prims.of_int (5))
                             (Prims.of_int (173)) (Prims.of_int (51)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (173)) (Prims.of_int (5))
                             (Prims.of_int (174)) (Prims.of_int (37)))))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (173)) (Prims.of_int (11))
                                   (Prims.of_int (173)) (Prims.of_int (51)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (173)) (Prims.of_int (5))
                                   (Prims.of_int (173)) (Prims.of_int (51)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (173))
                                         (Prims.of_int (45))
                                         (Prims.of_int (173))
                                         (Prims.of_int (50)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (173))
                                         (Prims.of_int (11))
                                         (Prims.of_int (173))
                                         (Prims.of_int (51)))))
                                (Obj.magic
                                   (Pulse_PP.pp Pulse_PP.printable_fstar_term
                                      ty))
                                (fun uu___ ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        FStar_Pprint.op_Hat_Slash_Hat
                                          (Pulse_PP.text
                                             "Expected term of type") uu___))))
                          (fun uu___ ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> FStar_Pprint.group uu___))))
                    (fun uu___ ->
                       (fun uu___ ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Pure.fst"
                                        (Prims.of_int (174))
                                        (Prims.of_int (5))
                                        (Prims.of_int (174))
                                        (Prims.of_int (37)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Pure.fst"
                                        (Prims.of_int (173))
                                        (Prims.of_int (5))
                                        (Prims.of_int (174))
                                        (Prims.of_int (37)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Pure.fst"
                                              (Prims.of_int (174))
                                              (Prims.of_int (11))
                                              (Prims.of_int (174))
                                              (Prims.of_int (37)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Pure.fst"
                                              (Prims.of_int (174))
                                              (Prims.of_int (5))
                                              (Prims.of_int (174))
                                              (Prims.of_int (37)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (174))
                                                    (Prims.of_int (32))
                                                    (Prims.of_int (174))
                                                    (Prims.of_int (36)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (174))
                                                    (Prims.of_int (11))
                                                    (Prims.of_int (174))
                                                    (Prims.of_int (37)))))
                                           (Obj.magic
                                              (Pulse_PP.pp
                                                 Pulse_PP.printable_fstar_term
                                                 t))
                                           (fun uu___1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pprint.op_Hat_Slash_Hat
                                                     (Pulse_PP.text
                                                        "got term") uu___1))))
                                     (fun uu___1 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 ->
                                             FStar_Pprint.group uu___1))))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       FStar_Pprint.op_Hat_Slash_Hat uu___
                                         uu___1)))) uu___)))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> [uu___]))
        | (FStar_Pervasives_Native.Some ty, FStar_Pervasives_Native.Some ty')
            ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (176)) (Prims.of_int (5))
                       (Prims.of_int (178)) (Prims.of_int (38)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (176)) (Prims.of_int (4))
                       (Prims.of_int (178)) (Prims.of_int (39)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (176)) (Prims.of_int (5))
                             (Prims.of_int (176)) (Prims.of_int (51)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                             (Prims.of_int (176)) (Prims.of_int (5))
                             (Prims.of_int (178)) (Prims.of_int (38)))))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (176)) (Prims.of_int (11))
                                   (Prims.of_int (176)) (Prims.of_int (51)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (176)) (Prims.of_int (5))
                                   (Prims.of_int (176)) (Prims.of_int (51)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (176))
                                         (Prims.of_int (45))
                                         (Prims.of_int (176))
                                         (Prims.of_int (50)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (176))
                                         (Prims.of_int (11))
                                         (Prims.of_int (176))
                                         (Prims.of_int (51)))))
                                (Obj.magic
                                   (Pulse_PP.pp Pulse_PP.printable_fstar_term
                                      ty))
                                (fun uu___ ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        FStar_Pprint.op_Hat_Slash_Hat
                                          (Pulse_PP.text
                                             "Expected term of type") uu___))))
                          (fun uu___ ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> FStar_Pprint.group uu___))))
                    (fun uu___ ->
                       (fun uu___ ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Pure.fst"
                                        (Prims.of_int (177))
                                        (Prims.of_int (5))
                                        (Prims.of_int (178))
                                        (Prims.of_int (38)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Pure.fst"
                                        (Prims.of_int (176))
                                        (Prims.of_int (5))
                                        (Prims.of_int (178))
                                        (Prims.of_int (38)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Pure.fst"
                                              (Prims.of_int (177))
                                              (Prims.of_int (5))
                                              (Prims.of_int (177))
                                              (Prims.of_int (37)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Pure.fst"
                                              (Prims.of_int (177))
                                              (Prims.of_int (5))
                                              (Prims.of_int (178))
                                              (Prims.of_int (38)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (177))
                                                    (Prims.of_int (11))
                                                    (Prims.of_int (177))
                                                    (Prims.of_int (37)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (177))
                                                    (Prims.of_int (5))
                                                    (Prims.of_int (177))
                                                    (Prims.of_int (37)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (177))
                                                          (Prims.of_int (32))
                                                          (Prims.of_int (177))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (177))
                                                          (Prims.of_int (11))
                                                          (Prims.of_int (177))
                                                          (Prims.of_int (37)))))
                                                 (Obj.magic
                                                    (Pulse_PP.pp
                                                       Pulse_PP.printable_fstar_term
                                                       t))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         FStar_Pprint.op_Hat_Slash_Hat
                                                           (Pulse_PP.text
                                                              "got term")
                                                           uu___1))))
                                           (fun uu___1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pprint.group uu___1))))
                                     (fun uu___1 ->
                                        (fun uu___1 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Pure.fst"
                                                         (Prims.of_int (178))
                                                         (Prims.of_int (5))
                                                         (Prims.of_int (178))
                                                         (Prims.of_int (38)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Pure.fst"
                                                         (Prims.of_int (177))
                                                         (Prims.of_int (5))
                                                         (Prims.of_int (178))
                                                         (Prims.of_int (38)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (178))
                                                               (Prims.of_int (11))
                                                               (Prims.of_int (178))
                                                               (Prims.of_int (38)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (178))
                                                               (Prims.of_int (5))
                                                               (Prims.of_int (178))
                                                               (Prims.of_int (38)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (37)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (38)))))
                                                            (Obj.magic
                                                               (Pulse_PP.pp
                                                                  Pulse_PP.printable_fstar_term
                                                                  ty'))
                                                            (fun uu___2 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___3
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "of type")
                                                                    uu___2))))
                                                      (fun uu___2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 ->
                                                              FStar_Pprint.group
                                                                uu___2))))
                                                (fun uu___2 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        FStar_Pprint.op_Hat_Slash_Hat
                                                          uu___1 uu___2))))
                                          uu___1)))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       FStar_Pprint.op_Hat_Slash_Hat uu___
                                         uu___1)))) uu___)))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> [uu___]))
let maybe_fail_doc :
  'uuuuu .
    FStar_Issue.issue Prims.list ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.range ->
          FStar_Pprint.document Prims.list ->
            ('uuuuu, unit) FStar_Tactics_Effect.tac_repr
  =
  fun issues ->
    fun g ->
      fun rng ->
        fun doc ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (183)) (Prims.of_int (6))
                     (Prims.of_int (187)) (Prims.of_int (14)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (189)) (Prims.of_int (2))
                     (Prims.of_int (192)) (Prims.of_int (32)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  FStar_List_Tot_Base.existsb
                    (fun i ->
                       ((FStar_Issue.level_of_issue i) = "Error") &&
                         (FStar_Pervasives_Native.uu___is_Some
                            (FStar_Issue.range_of_issue i))) issues))
            (fun uu___ ->
               (fun has_localized_error ->
                  if has_localized_error
                  then
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (190)) (Prims.of_int (41))
                                  (Prims.of_int (190)) (Prims.of_int (83)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (191)) (Prims.of_int (7))
                                  (Prims.of_int (191)) (Prims.of_int (21)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               FStar_Pprint.pretty_string
                                 Pulse_RuntimeUtils.float_one
                                 (Prims.of_int (80))
                                 (FStar_Pprint.concat doc)))
                         (fun message ->
                            FStar_Tactics_V2_Derived.fail message))
                  else
                    Obj.magic
                      (Pulse_Typing_Env.fail_doc g
                         (FStar_Pervasives_Native.Some rng) doc)) uu___)
let (instantiate_term_implicits :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term * Pulse_Syntax_Base.term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (195)) (Prims.of_int (10))
                 (Prims.of_int (195)) (Prims.of_int (20)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (195)) (Prims.of_int (23))
                 (Prims.of_int (219)) (Prims.of_int (14)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun f ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (196)) (Prims.of_int (11))
                            (Prims.of_int (196)) (Prims.of_int (23)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (196)) (Prims.of_int (26))
                            (Prims.of_int (219)) (Prims.of_int (14)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Elaborate_Pure.elab_term t0))
                   (fun uu___ ->
                      (fun rt ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (197))
                                       (Prims.of_int (12))
                                       (Prims.of_int (197))
                                       (Prims.of_int (31)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (197))
                                       (Prims.of_int (34))
                                       (Prims.of_int (219))
                                       (Prims.of_int (14)))))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ ->
                                    Pulse_RuntimeUtils.range_of_term t0))
                              (fun uu___ ->
                                 (fun rng ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (198))
                                                  (Prims.of_int (10))
                                                  (Prims.of_int (198))
                                                  (Prims.of_int (70)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (198))
                                                  (Prims.of_int (73))
                                                  (Prims.of_int (219))
                                                  (Prims.of_int (14)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (198))
                                                        (Prims.of_int (29))
                                                        (Prims.of_int (198))
                                                        (Prims.of_int (70)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (198))
                                                        (Prims.of_int (10))
                                                        (Prims.of_int (198))
                                                        (Prims.of_int (70)))))
                                               (Obj.magic
                                                  (Pulse_Typing_Env.get_range
                                                     g
                                                     (FStar_Pervasives_Native.Some
                                                        rng)))
                                               (fun uu___ ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       Pulse_RuntimeUtils.env_set_range
                                                         f uu___))))
                                         (fun uu___ ->
                                            (fun f1 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (199))
                                                             (Prims.of_int (21))
                                                             (Prims.of_int (199))
                                                             (Prims.of_int (74)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (198))
                                                             (Prims.of_int (73))
                                                             (Prims.of_int (219))
                                                             (Prims.of_int (14)))))
                                                    (Obj.magic
                                                       (catch_all
                                                          (fun uu___ ->
                                                             rtb_instantiate_implicits
                                                               g f1 rt)))
                                                    (fun uu___ ->
                                                       (fun uu___ ->
                                                          match uu___ with
                                                          | (topt, issues) ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (21)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (14)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.log_issues
                                                                    issues))
                                                                   (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match topt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    t0))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Could not infer implicit arguments in")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    [uu___2]))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    rng
                                                                    uu___2))
                                                                    uu___2)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (namedvs,
                                                                    t, ty) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    (FStar_List_Tot_Base.length
                                                                    namedvs)
                                                                    <>
                                                                    Prims.int_zero
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    t0))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "check_term: could not infer implicit arguments in")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    [uu___2]))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    [] g rng
                                                                    uu___2))
                                                                    uu___2))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (t, ty))))))
                                                                    uu___1)))
                                                         uu___))) uu___)))
                                   uu___))) uu___))) uu___)
let (instantiate_term_implicits_uvs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Typing_Env.env, Pulse_Syntax_Base.term, Pulse_Syntax_Base.term)
         FStar_Pervasives.dtuple3,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (222)) (Prims.of_int (10))
                 (Prims.of_int (222)) (Prims.of_int (20)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (222)) (Prims.of_int (23))
                 (Prims.of_int (251)) (Prims.of_int (20)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun f ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (223)) (Prims.of_int (11))
                            (Prims.of_int (223)) (Prims.of_int (23)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (223)) (Prims.of_int (26))
                            (Prims.of_int (251)) (Prims.of_int (20)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Elaborate_Pure.elab_term t0))
                   (fun uu___ ->
                      (fun rt ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (224))
                                       (Prims.of_int (12))
                                       (Prims.of_int (224))
                                       (Prims.of_int (31)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (224))
                                       (Prims.of_int (34))
                                       (Prims.of_int (251))
                                       (Prims.of_int (20)))))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ ->
                                    Pulse_RuntimeUtils.range_of_term t0))
                              (fun uu___ ->
                                 (fun rng ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (225))
                                                  (Prims.of_int (10))
                                                  (Prims.of_int (225))
                                                  (Prims.of_int (70)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (225))
                                                  (Prims.of_int (73))
                                                  (Prims.of_int (251))
                                                  (Prims.of_int (20)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (225))
                                                        (Prims.of_int (29))
                                                        (Prims.of_int (225))
                                                        (Prims.of_int (70)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (225))
                                                        (Prims.of_int (10))
                                                        (Prims.of_int (225))
                                                        (Prims.of_int (70)))))
                                               (Obj.magic
                                                  (Pulse_Typing_Env.get_range
                                                     g
                                                     (FStar_Pervasives_Native.Some
                                                        rng)))
                                               (fun uu___ ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       Pulse_RuntimeUtils.env_set_range
                                                         f uu___))))
                                         (fun uu___ ->
                                            (fun f1 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (226))
                                                             (Prims.of_int (21))
                                                             (Prims.of_int (226))
                                                             (Prims.of_int (74)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (225))
                                                             (Prims.of_int (73))
                                                             (Prims.of_int (251))
                                                             (Prims.of_int (20)))))
                                                    (Obj.magic
                                                       (catch_all
                                                          (fun uu___ ->
                                                             rtb_instantiate_implicits
                                                               g f1 rt)))
                                                    (fun uu___ ->
                                                       (fun uu___ ->
                                                          match uu___ with
                                                          | (topt, issues) ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (21)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (20)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.log_issues
                                                                    issues))
                                                                   (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match topt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    t0))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Could not infer implicit arguments in")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    [uu___2]))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    rng
                                                                    uu___2))
                                                                    uu___2))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (namedvs,
                                                                    t, ty) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.fold_left
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match 
                                                                    (uu___2,
                                                                    uu___3)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (uvs, t1,
                                                                    ty1),
                                                                    (namedv,
                                                                    namedvt))
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing_Env.push_binding
                                                                    uvs
                                                                    (Pulse_Typing_Env.fresh
                                                                    (Pulse_Typing_Env.push_env
                                                                    g uvs))
                                                                    {
                                                                    Pulse_Syntax_Base.name
                                                                    =
                                                                    ((FStar_Reflection_V2_Builtins.inspect_namedv
                                                                    namedv).FStar_Reflection_V2_Data.ppname);
                                                                    Pulse_Syntax_Base.range
                                                                    = rng
                                                                    } namedvt),
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    t1
                                                                    [
                                                                    Pulse_Syntax_Naming.NT
                                                                    (((FStar_Reflection_V2_Builtins.inspect_namedv
                                                                    namedv).FStar_Reflection_V2_Data.uniq),
                                                                    (Pulse_Syntax_Pure.tm_var
                                                                    {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    =
                                                                    (Pulse_Typing_Env.fresh
                                                                    (Pulse_Typing_Env.push_env
                                                                    g uvs));
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.name
                                                                    =
                                                                    ((FStar_Reflection_V2_Builtins.inspect_namedv
                                                                    namedv).FStar_Reflection_V2_Data.ppname);
                                                                    Pulse_Syntax_Base.range
                                                                    = rng
                                                                    }
                                                                    }))]),
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    ty1
                                                                    [
                                                                    Pulse_Syntax_Naming.NT
                                                                    (((FStar_Reflection_V2_Builtins.inspect_namedv
                                                                    namedv).FStar_Reflection_V2_Data.uniq),
                                                                    (Pulse_Syntax_Pure.tm_var
                                                                    {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    =
                                                                    (Pulse_Typing_Env.fresh
                                                                    (Pulse_Typing_Env.push_env
                                                                    g uvs));
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.name
                                                                    =
                                                                    ((FStar_Reflection_V2_Builtins.inspect_namedv
                                                                    namedv).FStar_Reflection_V2_Data.ppname);
                                                                    Pulse_Syntax_Base.range
                                                                    = rng
                                                                    }
                                                                    }))])))))
                                                                    uu___3
                                                                    uu___2)
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)), t,
                                                                    ty))
                                                                    namedvs))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (uvs, t1,
                                                                    ty1) ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (uvs, t1,
                                                                    ty1)))))
                                                                    uu___1)))
                                                         uu___))) uu___)))
                                   uu___))) uu___))) uu___)
let (check_universe :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.universe, unit) Prims.dtuple2, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (255)) (Prims.of_int (12))
                 (Prims.of_int (255)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (255)) (Prims.of_int (25))
                 (Prims.of_int (270)) (Prims.of_int (23)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun f ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (256)) (Prims.of_int (13))
                            (Prims.of_int (256)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (256)) (Prims.of_int (27))
                            (Prims.of_int (270)) (Prims.of_int (23)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                   (fun uu___ ->
                      (fun rt ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (257))
                                       (Prims.of_int (25))
                                       (Prims.of_int (257))
                                       (Prims.of_int (68)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (256))
                                       (Prims.of_int (27))
                                       (Prims.of_int (270))
                                       (Prims.of_int (23)))))
                              (Obj.magic
                                 (catch_all
                                    (fun uu___ -> rtb_universe_of g f rt)))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    match uu___ with
                                    | (ru_opt, issues) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (258))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (258))
                                                      (Prims.of_int (23)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (259))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (270))
                                                      (Prims.of_int (23)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Builtins.log_issues
                                                   issues))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match ru_opt with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (81)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (81)))))
                                                               (Obj.magic
                                                                  (ill_typed_term
                                                                    t
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Pure.tm_type
                                                                    Pulse_Syntax_Pure.u_unknown))
                                                                    FStar_Pervasives_Native.None))
                                                               (fun uu___2 ->
                                                                  (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t) uu___2))
                                                                    uu___2)))
                                                   | FStar_Pervasives_Native.Some
                                                       ru ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  Prims.Mkdtuple2
                                                                    (ru, ())))))
                                                  uu___1))) uu___))) uu___)))
             uu___)
let (tc_meta_callback :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((FStar_Reflection_Types.term, FStar_TypeChecker_Core.tot_or_ghost,
           FStar_Reflection_Types.term,
           (unit, unit, unit) FStar_Reflection_Typing.typing)
           FStar_Pervasives.dtuple4 FStar_Pervasives_Native.option *
           FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (275)) (Prims.of_int (6))
                   (Prims.of_int (280)) (Prims.of_int (14)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (274)) (Prims.of_int (8))
                   (Prims.of_int (274)) (Prims.of_int (11)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (275)) (Prims.of_int (12))
                         (Prims.of_int (275)) (Prims.of_int (50)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (275)) (Prims.of_int (6))
                         (Prims.of_int (280)) (Prims.of_int (14)))))
                (Obj.magic (catch_all (fun uu___ -> rtb_tc_term g f e)))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        match uu___ with
                        | (FStar_Pervasives_Native.None, issues) ->
                            (FStar_Pervasives_Native.None, issues)
                        | (FStar_Pervasives_Native.Some (e1, (eff, t)),
                           issues) ->
                            ((FStar_Pervasives_Native.Some
                                (FStar_Pervasives.Mkdtuple4
                                   (e1, eff, t,
                                     (FStar_Reflection_Typing.T_Token
                                        (f, e1, (eff, t), ()))))), issues)))))
          (fun res -> FStar_Tactics_Effect.lift_div_tac (fun uu___ -> res))
let (compute_term_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, FStar_TypeChecker_Core.tot_or_ghost,
         Pulse_Syntax_Base.term, unit) FStar_Pervasives.dtuple4,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (289)) (Prims.of_int (13))
                 (Prims.of_int (289)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (289)) (Prims.of_int (26))
                 (Prims.of_int (301)) (Prims.of_int (63)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun fg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (290)) (Prims.of_int (13))
                            (Prims.of_int (290)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (291)) (Prims.of_int (4))
                            (Prims.of_int (301)) (Prims.of_int (63)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                   (fun uu___ ->
                      (fun rt ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (291))
                                       (Prims.of_int (4))
                                       (Prims.of_int (294))
                                       (Prims.of_int (44)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (294))
                                       (Prims.of_int (45))
                                       (Prims.of_int (301))
                                       (Prims.of_int (63)))))
                              (Obj.magic
                                 (debug g
                                    (fun uu___ ->
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (294))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (294))
                                                  (Prims.of_int (43)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (292))
                                                  (Prims.of_int (12))
                                                  (Prims.of_int (294))
                                                  (Prims.of_int (43)))))
                                         (Obj.magic
                                            (FStar_Tactics_V2_Builtins.term_to_string
                                               rt))
                                         (fun uu___1 ->
                                            (fun uu___1 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (292))
                                                             (Prims.of_int (12))
                                                             (Prims.of_int (294))
                                                             (Prims.of_int (43)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (292))
                                                             (Prims.of_int (12))
                                                             (Prims.of_int (294))
                                                             (Prims.of_int (43)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (293))
                                                                   (Prims.of_int (22))
                                                                   (Prims.of_int (293))
                                                                   (Prims.of_int (42)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Printf.fst"
                                                                   (Prims.of_int (122))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (124))
                                                                   (Prims.of_int (44)))))
                                                          (Obj.magic
                                                             (Pulse_Syntax_Printer.term_to_string
                                                                t))
                                                          (fun uu___2 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___3 ->
                                                                  fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_tot : called on "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " elaborated to "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            uu___2 uu___1))))
                                              uu___1))))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (295))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (295))
                                                  (Prims.of_int (46)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (294))
                                                  (Prims.of_int (45))
                                                  (Prims.of_int (301))
                                                  (Prims.of_int (63)))))
                                         (Obj.magic
                                            (tc_meta_callback g fg rt))
                                         (fun uu___1 ->
                                            (fun uu___1 ->
                                               match uu___1 with
                                               | (res, issues) ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Pure.fst"
                                                                 (Prims.of_int (296))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (296))
                                                                 (Prims.of_int (23)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Pure.fst"
                                                                 (Prims.of_int (297))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (301))
                                                                 (Prims.of_int (63)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Builtins.log_issues
                                                              issues))
                                                        (fun uu___2 ->
                                                           (fun uu___2 ->
                                                              match res with
                                                              | FStar_Pervasives_Native.None
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (ill_typed_term
                                                                    t
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t) uu___3))
                                                                    uu___3)))
                                                              | FStar_Pervasives_Native.Some
                                                                  (FStar_Pervasives.Mkdtuple4
                                                                  (rt1, eff,
                                                                   ty', tok))
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (rt1,
                                                                    eff, ty',
                                                                    ())))))
                                                             uu___2))) uu___1)))
                                   uu___))) uu___))) uu___)
let (compute_term_type_and_u :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, FStar_TypeChecker_Core.tot_or_ghost,
         Pulse_Syntax_Base.term,
         (Pulse_Syntax_Base.universe, unit) Prims.dtuple2, unit)
         FStar_Pervasives.dtuple5,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (310)) (Prims.of_int (13))
                 (Prims.of_int (310)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (310)) (Prims.of_int (26))
                 (Prims.of_int (321)) (Prims.of_int (45)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun fg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (311)) (Prims.of_int (13))
                            (Prims.of_int (311)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (311)) (Prims.of_int (27))
                            (Prims.of_int (321)) (Prims.of_int (45)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                   (fun uu___ ->
                      (fun rt ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (312))
                                       (Prims.of_int (22))
                                       (Prims.of_int (312))
                                       (Prims.of_int (46)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (311))
                                       (Prims.of_int (27))
                                       (Prims.of_int (321))
                                       (Prims.of_int (45)))))
                              (Obj.magic (tc_meta_callback g fg rt))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    match uu___ with
                                    | (res, issues) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (313))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (313))
                                                      (Prims.of_int (23)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (314))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (321))
                                                      (Prims.of_int (45)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Builtins.log_issues
                                                   issues))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match res with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (59)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (59)))))
                                                            (Obj.magic
                                                               (ill_typed_term
                                                                  t
                                                                  FStar_Pervasives_Native.None
                                                                  FStar_Pervasives_Native.None))
                                                            (fun uu___2 ->
                                                               (fun uu___2 ->
                                                                  Obj.magic
                                                                    (
                                                                    maybe_fail_doc
                                                                    issues g
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t) uu___2))
                                                                 uu___2))
                                                   | FStar_Pervasives_Native.Some
                                                       (FStar_Pervasives.Mkdtuple4
                                                       (rt1, eff, ty', tok))
                                                       ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (45)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (45)))))
                                                            (Obj.magic
                                                               (check_universe
                                                                  g ty'))
                                                            (fun uu___2 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___3
                                                                    ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u, uty)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (rt1,
                                                                    eff, ty',
                                                                    (Prims.Mkdtuple2
                                                                    (u, ())),
                                                                    ())))))
                                                  uu___1))) uu___))) uu___)))
             uu___)
let (check_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      FStar_TypeChecker_Core.tot_or_ghost ->
        Pulse_Syntax_Base.term ->
          ((Pulse_Syntax_Base.term, unit) Prims.dtuple2, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun eff ->
        fun t ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (326)) (Prims.of_int (13))
                     (Prims.of_int (326)) (Prims.of_int (43)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (324)) (Prims.of_int (39))
                     (Prims.of_int (343)) (Prims.of_int (78)))))
            (Obj.magic (instantiate_term_implicits g e))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | (e1, uu___1) ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Pure.fst"
                                    (Prims.of_int (328)) (Prims.of_int (11))
                                    (Prims.of_int (328)) (Prims.of_int (21)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Pure.fst"
                                    (Prims.of_int (328)) (Prims.of_int (24))
                                    (Prims.of_int (343)) (Prims.of_int (78)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 -> Pulse_Typing.elab_env g))
                           (fun uu___2 ->
                              (fun fg ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (329))
                                               (Prims.of_int (11))
                                               (Prims.of_int (329))
                                               (Prims.of_int (22)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (329))
                                               (Prims.of_int (25))
                                               (Prims.of_int (343))
                                               (Prims.of_int (78)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Pulse_Elaborate_Pure.elab_term e1))
                                      (fun uu___2 ->
                                         (fun re ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (330))
                                                          (Prims.of_int (11))
                                                          (Prims.of_int (330))
                                                          (Prims.of_int (22)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (330))
                                                          (Prims.of_int (25))
                                                          (Prims.of_int (343))
                                                          (Prims.of_int (78)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       Pulse_Elaborate_Pure.elab_term
                                                         t))
                                                 (fun uu___2 ->
                                                    (fun rt ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (22)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (78)))))
                                                            (Obj.magic
                                                               (catch_all
                                                                  (fun uu___2
                                                                    ->
                                                                    rtb_core_check_term
                                                                    (Pulse_Typing_Env.push_context
                                                                    g
                                                                    "check_term_with_expected_type_and_effect"
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    rt)) fg
                                                                    re eff rt)))
                                                            (fun uu___2 ->
                                                               (fun uu___2 ->
                                                                  match uu___2
                                                                  with
                                                                  | (topt,
                                                                    issues)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.log_issues
                                                                    issues))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match topt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (ill_typed_term
                                                                    e1
                                                                    (FStar_Pervasives_Native.Some
                                                                    t)
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    e1)
                                                                    uu___4))
                                                                    uu___4)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tok ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.Mkdtuple2
                                                                    (e1, ())))))
                                                                    uu___3)))
                                                                 uu___2)))
                                                      uu___2))) uu___2)))
                                uu___2))) uu___)
let (check_term_at_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        ((Pulse_Syntax_Base.term, FStar_TypeChecker_Core.tot_or_ghost, 
           unit) FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (348)) (Prims.of_int (13))
                   (Prims.of_int (348)) (Prims.of_int (43)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (346)) (Prims.of_int (60))
                   (Prims.of_int (365)) (Prims.of_int (65)))))
          (Obj.magic (instantiate_term_implicits g e))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | (e1, uu___1) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (349)) (Prims.of_int (11))
                                  (Prims.of_int (349)) (Prims.of_int (21)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (349)) (Prims.of_int (24))
                                  (Prims.of_int (365)) (Prims.of_int (65)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> Pulse_Typing.elab_env g))
                         (fun uu___2 ->
                            (fun fg ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (350))
                                             (Prims.of_int (11))
                                             (Prims.of_int (350))
                                             (Prims.of_int (22)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (350))
                                             (Prims.of_int (25))
                                             (Prims.of_int (365))
                                             (Prims.of_int (65)))))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          Pulse_Elaborate_Pure.elab_term e1))
                                    (fun uu___2 ->
                                       (fun re ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (351))
                                                        (Prims.of_int (11))
                                                        (Prims.of_int (351))
                                                        (Prims.of_int (22)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (351))
                                                        (Prims.of_int (25))
                                                        (Prims.of_int (365))
                                                        (Prims.of_int (65)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     Pulse_Elaborate_Pure.elab_term
                                                       t))
                                               (fun uu___2 ->
                                                  (fun rt ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (354))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (357))
                                                                   (Prims.of_int (15)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (351))
                                                                   (Prims.of_int (25))
                                                                   (Prims.of_int (365))
                                                                   (Prims.of_int (65)))))
                                                          (Obj.magic
                                                             (catch_all
                                                                (fun uu___2
                                                                   ->
                                                                   rtb_core_check_term_at_type
                                                                    (Pulse_Typing_Env.push_context
                                                                    g
                                                                    "check_term_with_expected_type"
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    rt)) fg
                                                                    re rt)))
                                                          (fun uu___2 ->
                                                             (fun uu___2 ->
                                                                match uu___2
                                                                with
                                                                | (effopt,
                                                                   issues) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.log_issues
                                                                    issues))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match effopt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (ill_typed_term
                                                                    e1
                                                                    (FStar_Pervasives_Native.Some
                                                                    t)
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    e1)
                                                                    uu___4))
                                                                    uu___4)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    eff ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e1, eff,
                                                                    ())))))
                                                                    uu___3)))
                                                               uu___2)))
                                                    uu___2))) uu___2)))
                              uu___2))) uu___)
let (tc_with_core :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (((FStar_TypeChecker_Core.tot_or_ghost, FStar_Reflection_Types.term,
           (unit, unit, unit) FStar_Reflection_Typing.typing)
           FStar_Pervasives.dtuple3 FStar_Pervasives_Native.option *
           FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun f ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (369)) (Prims.of_int (23))
                   (Prims.of_int (369)) (Prims.of_int (124)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (369)) (Prims.of_int (3))
                   (Prims.of_int (373)) (Prims.of_int (76)))))
          (Obj.magic
             (catch_all
                (fun uu___ ->
                   rtb_core_compute_term_type
                     (Pulse_Typing_Env.push_context g "tc_with_core"
                        (FStar_Reflection_V2_Builtins.range_of_term e)) f e)))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  match uu___ with
                  | (ropt, issues) ->
                      (match ropt with
                       | FStar_Pervasives_Native.None ->
                           (FStar_Pervasives_Native.None, issues)
                       | FStar_Pervasives_Native.Some (eff, t) ->
                           ((FStar_Pervasives_Native.Some
                               (FStar_Pervasives.Mkdtuple3
                                  (eff, t,
                                    (FStar_Reflection_Typing.T_Token
                                       (f, e, (eff, t), ()))))), issues))))
let (core_compute_term_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((FStar_TypeChecker_Core.tot_or_ghost, Pulse_Syntax_Base.term, 
         unit) FStar_Pervasives.dtuple3,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (379)) (Prims.of_int (13))
                 (Prims.of_int (379)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (379)) (Prims.of_int (26))
                 (Prims.of_int (388)) (Prims.of_int (55)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun fg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (380)) (Prims.of_int (13))
                            (Prims.of_int (380)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                            (Prims.of_int (380)) (Prims.of_int (27))
                            (Prims.of_int (388)) (Prims.of_int (55)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                   (fun uu___ ->
                      (fun rt ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (381))
                                       (Prims.of_int (22))
                                       (Prims.of_int (381))
                                       (Prims.of_int (94)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (380))
                                       (Prims.of_int (27))
                                       (Prims.of_int (388))
                                       (Prims.of_int (55)))))
                              (Obj.magic
                                 (tc_with_core
                                    (Pulse_Typing_Env.push_context g
                                       "core_check_term"
                                       (FStar_Reflection_V2_Builtins.range_of_term
                                          rt)) fg rt))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    match uu___ with
                                    | (res, issues) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (382))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (382))
                                                      (Prims.of_int (23)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (383))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (388))
                                                      (Prims.of_int (55)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Builtins.log_issues
                                                   issues))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match res with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (59)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (59)))))
                                                               (Obj.magic
                                                                  (ill_typed_term
                                                                    t
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Pervasives_Native.None))
                                                               (fun uu___2 ->
                                                                  (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t) uu___2))
                                                                    uu___2)))
                                                   | FStar_Pervasives_Native.Some
                                                       (FStar_Pervasives.Mkdtuple3
                                                       (eff, ty', tok)) ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  FStar_Pervasives.Mkdtuple3
                                                                    (eff,
                                                                    ty', ())))))
                                                  uu___1))) uu___))) uu___)))
             uu___)
let (core_check_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      FStar_TypeChecker_Core.tot_or_ghost ->
        Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun eff ->
        fun t ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (391)) (Prims.of_int (11))
                     (Prims.of_int (391)) (Prims.of_int (21)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (391)) (Prims.of_int (24))
                     (Prims.of_int (405)) (Prims.of_int (69)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_Typing.elab_env g))
            (fun uu___ ->
               (fun fg ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (392)) (Prims.of_int (11))
                                (Prims.of_int (392)) (Prims.of_int (22)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (392)) (Prims.of_int (25))
                                (Prims.of_int (405)) (Prims.of_int (69)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ -> Pulse_Elaborate_Pure.elab_term e))
                       (fun uu___ ->
                          (fun re ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (393))
                                           (Prims.of_int (11))
                                           (Prims.of_int (393))
                                           (Prims.of_int (22)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (393))
                                           (Prims.of_int (25))
                                           (Prims.of_int (405))
                                           (Prims.of_int (69)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ ->
                                        Pulse_Elaborate_Pure.elab_term t))
                                  (fun uu___ ->
                                     (fun rt ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (395))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (398))
                                                      (Prims.of_int (20)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (393))
                                                      (Prims.of_int (25))
                                                      (Prims.of_int (405))
                                                      (Prims.of_int (69)))))
                                             (Obj.magic
                                                (catch_all
                                                   (fun uu___ ->
                                                      rtb_core_check_term
                                                        (Pulse_Typing_Env.push_context
                                                           g
                                                           "core_check_term"
                                                           (FStar_Reflection_V2_Builtins.range_of_term
                                                              rt)) fg re eff
                                                        rt)))
                                             (fun uu___ ->
                                                (fun uu___ ->
                                                   match uu___ with
                                                   | (topt, issues) ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (21)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (69)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_V2_Builtins.log_issues
                                                                  issues))
                                                            (fun uu___1 ->
                                                               (fun uu___1 ->
                                                                  match topt
                                                                  with
                                                                  | FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (ill_typed_term
                                                                    e
                                                                    (FStar_Pervasives_Native.Some
                                                                    t)
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    e) uu___2))
                                                                    uu___2)))
                                                                  | FStar_Pervasives_Native.Some
                                                                    tok ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))))
                                                                 uu___1)))
                                                  uu___))) uu___))) uu___)))
                 uu___)
let (core_check_term_at_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        ((FStar_TypeChecker_Core.tot_or_ghost, unit) Prims.dtuple2, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (408)) (Prims.of_int (11))
                   (Prims.of_int (408)) (Prims.of_int (21)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (408)) (Prims.of_int (24))
                   (Prims.of_int (423)) (Prims.of_int (62)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Typing.elab_env g))
          (fun uu___ ->
             (fun fg ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (409)) (Prims.of_int (11))
                              (Prims.of_int (409)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                              (Prims.of_int (409)) (Prims.of_int (25))
                              (Prims.of_int (423)) (Prims.of_int (62)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Pulse_Elaborate_Pure.elab_term e))
                     (fun uu___ ->
                        (fun re ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (410))
                                         (Prims.of_int (11))
                                         (Prims.of_int (410))
                                         (Prims.of_int (22)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (410))
                                         (Prims.of_int (25))
                                         (Prims.of_int (423))
                                         (Prims.of_int (62)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      Pulse_Elaborate_Pure.elab_term t))
                                (fun uu___ ->
                                   (fun rt ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (412))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (415))
                                                    (Prims.of_int (16)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (410))
                                                    (Prims.of_int (25))
                                                    (Prims.of_int (423))
                                                    (Prims.of_int (62)))))
                                           (Obj.magic
                                              (catch_all
                                                 (fun uu___ ->
                                                    rtb_core_check_term_at_type
                                                      (Pulse_Typing_Env.push_context
                                                         g
                                                         "core_check_term_at_type"
                                                         (FStar_Reflection_V2_Builtins.range_of_term
                                                            rt)) fg re rt)))
                                           (fun uu___ ->
                                              (fun uu___ ->
                                                 match uu___ with
                                                 | (effopt, issues) ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (416))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (416))
                                                                   (Prims.of_int (21)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (417))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (423))
                                                                   (Prims.of_int (62)))))
                                                          (Obj.magic
                                                             (FStar_Tactics_V2_Builtins.log_issues
                                                                issues))
                                                          (fun uu___1 ->
                                                             (fun uu___1 ->
                                                                match effopt
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (ill_typed_term
                                                                    e
                                                                    (FStar_Pervasives_Native.Some
                                                                    t)
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (maybe_fail_doc
                                                                    issues g
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    e) uu___2))
                                                                    uu___2)))
                                                                | FStar_Pervasives_Native.Some
                                                                    eff ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.Mkdtuple2
                                                                    (eff, ())))))
                                                               uu___1)))
                                                uu___))) uu___))) uu___)))
               uu___)
let (check_vprop :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, unit) Prims.dtuple2, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      check_term (Pulse_Typing_Env.push_context_no_range g "check_vprop") t
        FStar_TypeChecker_Core.E_Total Pulse_Syntax_Pure.tm_vprop
let (check_vprop_with_core :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      core_check_term
        (Pulse_Typing_Env.push_context_no_range g "check_vprop_with_core") t
        FStar_TypeChecker_Core.E_Total Pulse_Syntax_Pure.tm_vprop
let (try_get_non_informative_witness :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        unit ->
          ((unit, unit, unit) Pulse_Typing.non_informative_t
             FStar_Pervasives_Native.option,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun u ->
      fun ty ->
        fun ty_typing ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (452)) (Prims.of_int (15))
                     (Prims.of_int (452)) (Prims.of_int (41)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (452)) (Prims.of_int (44))
                     (Prims.of_int (473)) (Prims.of_int (5)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_Typing.non_informative_class u ty))
            (fun uu___ ->
               (fun goal ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (453)) (Prims.of_int (17))
                                (Prims.of_int (453)) (Prims.of_int (31)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (453)) (Prims.of_int (34))
                                (Prims.of_int (473)) (Prims.of_int (5)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ -> Pulse_Elaborate_Pure.elab_term goal))
                       (fun uu___ ->
                          (fun r_goal ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (454))
                                           (Prims.of_int (16))
                                           (Prims.of_int (454))
                                           (Prims.of_int (26)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Pure.fst"
                                           (Prims.of_int (454))
                                           (Prims.of_int (29))
                                           (Prims.of_int (473))
                                           (Prims.of_int (5)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ -> Pulse_Typing.elab_env g))
                                  (fun uu___ ->
                                     (fun r_env ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (455))
                                                      (Prims.of_int (28))
                                                      (Prims.of_int (455))
                                                      (Prims.of_int (73)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Pure.fst"
                                                      (Prims.of_int (458))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (473))
                                                      (Prims.of_int (5)))))
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___ -> ()))
                                             (fun uu___ ->
                                                (fun constraint_typing ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Pure.fst"
                                                                 (Prims.of_int (459))
                                                                 (Prims.of_int (12))
                                                                 (Prims.of_int (459))
                                                                 (Prims.of_int (76)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Pure.fst"
                                                                 (Prims.of_int (460))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (473))
                                                                 (Prims.of_int (5)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Builtins.call_subtac
                                                              r_env
                                                              FStar_Tactics_Typeclasses.tcresolve
                                                              u r_goal))
                                                        (fun uu___ ->
                                                           (fun r ->
                                                              match r with
                                                              | (FStar_Pervasives_Native.None,
                                                                 issues) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.log_issues
                                                                    issues))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Pervasives_Native.None))))
                                                              | (FStar_Pervasives_Native.Some
                                                                 r_dict,
                                                                 uu___) ->
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Pure.wr
                                                                    r_dict
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    ty)), ()))))))
                                                             uu___))) uu___)))
                                       uu___))) uu___))) uu___)
let (get_non_informative_witness :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        unit ->
          ((unit, unit, unit) Pulse_Typing.non_informative_t, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun u ->
      fun t ->
        fun t_typing ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (477)) (Prims.of_int (10))
                     (Prims.of_int (477)) (Prims.of_int (56)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                     (Prims.of_int (477)) (Prims.of_int (4))
                     (Prims.of_int (484)) (Prims.of_int (17)))))
            (Obj.magic (try_get_non_informative_witness g u t ()))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | FStar_Pervasives_Native.None ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (480))
                                       (Prims.of_int (45))
                                       (Prims.of_int (483))
                                       (Prims.of_int (7)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (480))
                                       (Prims.of_int (6))
                                       (Prims.of_int (483))
                                       (Prims.of_int (7)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (481))
                                             (Prims.of_int (8))
                                             (Prims.of_int (482))
                                             (Prims.of_int (18)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Pure.fst"
                                             (Prims.of_int (480))
                                             (Prims.of_int (45))
                                             (Prims.of_int (483))
                                             (Prims.of_int (7)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Pure.fst"
                                                   (Prims.of_int (482))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (482))
                                                   (Prims.of_int (18)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Pure.fst"
                                                   (Prims.of_int (481))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (482))
                                                   (Prims.of_int (18)))))
                                          (Obj.magic
                                             (Pulse_PP.pp
                                                Pulse_PP.printable_fstar_term
                                                t))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  FStar_Pprint.op_Hat_Slash_Hat
                                                    (Pulse_PP.text
                                                       "Expected a term with a non-informative (e.g., erased) type; got")
                                                    uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 -> [uu___1]))))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    Obj.magic
                                      (Pulse_Typing_Env.fail_doc g
                                         (FStar_Pervasives_Native.Some
                                            (Pulse_RuntimeUtils.range_of_term
                                               t)) uu___1)) uu___1)))
                  | FStar_Pervasives_Native.Some e ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> e)))) uu___)
let (try_check_prop_validity :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        (unit FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      fun uu___ ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (488)) (Prims.of_int (24))
                   (Prims.of_int (488)) (Prims.of_int (81)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (488)) (Prims.of_int (3))
                   (Prims.of_int (489)) (Prims.of_int (9)))))
          (Obj.magic
             (rtb_check_prop_validity g true (Pulse_Typing.elab_env g)
                (Pulse_Elaborate_Pure.elab_term p)))
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> match uu___1 with | (t_opt, issues) -> t_opt))
let (check_prop_validity :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      fun uu___ ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (493)) (Prims.of_int (24))
                   (Prims.of_int (493)) (Prims.of_int (82)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (493)) (Prims.of_int (3))
                   (Prims.of_int (500)) (Prims.of_int (21)))))
          (Obj.magic
             (rtb_check_prop_validity g false (Pulse_Typing.elab_env g)
                (Pulse_Elaborate_Pure.elab_term p)))
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (t_opt, issues) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (494)) (Prims.of_int (4))
                                  (Prims.of_int (494)) (Prims.of_int (23)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (495)) (Prims.of_int (4))
                                  (Prims.of_int (500)) (Prims.of_int (21)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.log_issues issues))
                         (fun uu___2 ->
                            (fun uu___2 ->
                               match t_opt with
                               | FStar_Pervasives_Native.None ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (499))
                                                    (Prims.of_int (21))
                                                    (Prims.of_int (499))
                                                    (Prims.of_int (64)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Pure.fst"
                                                    (Prims.of_int (498))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (499))
                                                    (Prims.of_int (64)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (499))
                                                          (Prims.of_int (22))
                                                          (Prims.of_int (499))
                                                          (Prims.of_int (63)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (499))
                                                          (Prims.of_int (21))
                                                          (Prims.of_int (499))
                                                          (Prims.of_int (64)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Pure.fst"
                                                                (Prims.of_int (499))
                                                                (Prims.of_int (59))
                                                                (Prims.of_int (499))
                                                                (Prims.of_int (63)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Pure.fst"
                                                                (Prims.of_int (499))
                                                                (Prims.of_int (22))
                                                                (Prims.of_int (499))
                                                                (Prims.of_int (63)))))
                                                       (Obj.magic
                                                          (Pulse_PP.pp
                                                             Pulse_PP.printable_fstar_term
                                                             p))
                                                       (fun uu___3 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               FStar_Pprint.op_Hat_Slash_Hat
                                                                 (Pulse_PP.text
                                                                    "Failed to prove property:")
                                                                 uu___3))))
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 -> [uu___3]))))
                                           (fun uu___3 ->
                                              (fun uu___3 ->
                                                 Obj.magic
                                                   (maybe_fail_doc issues g
                                                      (Pulse_RuntimeUtils.range_of_term
                                                         p) uu___3)) uu___3)))
                               | FStar_Pervasives_Native.Some tok ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> ())))) uu___2)))
               uu___1)
let fail_expected_tot_found_ghost :
  'uuuuu .
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term -> ('uuuuu, unit) FStar_Tactics_Effect.tac_repr
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (504)) (Prims.of_int (4)) (Prims.of_int (504))
                 (Prims.of_int (86)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (503)) (Prims.of_int (2)) (Prims.of_int (504))
                 (Prims.of_int (86)))))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                       (Prims.of_int (504)) (Prims.of_int (65))
                       (Prims.of_int (504)) (Prims.of_int (85)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                       (Prims.of_int (19)) (Prims.of_int (590))
                       (Prims.of_int (31)))))
              (Obj.magic (Pulse_Syntax_Printer.term_to_string t))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      Prims.strcat "Expected a total term, found ghost term "
                        (Prims.strcat uu___ "")))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (Pulse_Typing_Env.fail g
                   (FStar_Pervasives_Native.Some
                      (Pulse_RuntimeUtils.range_of_term t)) uu___)) uu___)
let (compute_tot_term_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, Pulse_Syntax_Base.typ, unit)
         FStar_Pervasives.dtuple3,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (507)) (Prims.of_int (35))
                 (Prims.of_int (507)) (Prims.of_int (56)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (506)) (Prims.of_int (31))
                 (Prims.of_int (509)) (Prims.of_int (40)))))
        (Obj.magic (compute_term_type g t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives.Mkdtuple4 (t1, eff, ty, t_typing) ->
                  if eff = FStar_TypeChecker_Core.E_Total
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Pervasives.Mkdtuple3 (t1, ty, ()))))
                  else
                    Obj.magic (Obj.repr (fail_expected_tot_found_ghost g t1)))
             uu___)
let (compute_tot_term_type_and_u :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term, Pulse_Syntax_Base.universe,
         Pulse_Syntax_Base.typ, unit, unit) FStar_Pervasives.dtuple5,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (512)) (Prims.of_int (55))
                 (Prims.of_int (512)) (Prims.of_int (82)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (511)) (Prims.of_int (37))
                 (Prims.of_int (514)) (Prims.of_int (40)))))
        (Obj.magic (compute_term_type_and_u g t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives.Mkdtuple5
                  (t1, eff, ty, Prims.Mkdtuple2 (u, ty_typing), t_typing) ->
                  if eff = FStar_TypeChecker_Core.E_Total
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Pervasives.Mkdtuple5 (t1, u, ty, (), ()))))
                  else
                    Obj.magic (Obj.repr (fail_expected_tot_found_ghost g t1)))
             uu___)
let (check_tot_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        ((Pulse_Syntax_Base.term, unit) Prims.dtuple2, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g -> fun e -> fun t -> check_term g e FStar_TypeChecker_Core.E_Total t
let (core_compute_tot_term_type :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.typ, unit) Prims.dtuple2, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (520)) (Prims.of_int (25))
                 (Prims.of_int (520)) (Prims.of_int (51)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (519)) (Prims.of_int (36))
                 (Prims.of_int (522)) (Prims.of_int (40)))))
        (Obj.magic (core_compute_term_type g t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives.Mkdtuple3 (eff, ty, d) ->
                  if eff = FStar_TypeChecker_Core.E_Total
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> Prims.Mkdtuple2 (ty, ()))))
                  else
                    Obj.magic (Obj.repr (fail_expected_tot_found_ghost g t)))
             uu___)
let (core_check_tot_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.typ -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e -> fun t -> core_check_term g e FStar_TypeChecker_Core.E_Total t
let (is_non_informative :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp ->
      ((unit, unit) FStar_Tactics_Types.non_informative_token
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (528)) (Prims.of_int (21))
                 (Prims.of_int (528)) (Prims.of_int (89)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (527)) (Prims.of_int (28))
                 (Prims.of_int (530)) (Prims.of_int (6)))))
        (Obj.magic
           (catch_all
              (fun uu___ ->
                 FStar_Tactics_V2_Builtins.is_non_informative
                   (Pulse_Typing.elab_env g)
                   (Pulse_Elaborate_Pure.elab_comp c))))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (ropt, issues) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (529)) (Prims.of_int (2))
                                (Prims.of_int (529)) (Prims.of_int (21)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                (Prims.of_int (528)) (Prims.of_int (6))
                                (Prims.of_int (528)) (Prims.of_int (10)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Builtins.log_issues issues))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> ropt)))) uu___)
let (check_subtyping :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        ((unit, unit, unit) Pulse_Typing.subtyping_token, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_V2_Derived.with_policy FStar_Tactics_Types.SMTSync
          (fun uu___ ->
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (534)) (Prims.of_int (20))
                        (Prims.of_int (534)) (Prims.of_int (47)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (533)) (Prims.of_int (34))
                        (Prims.of_int (542)) (Prims.of_int (47)))))
               (Obj.magic (rtb_check_subtyping g t1 t2))
               (fun uu___1 ->
                  (fun uu___1 ->
                     match uu___1 with
                     | (res, issues) ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (535))
                                       (Prims.of_int (2))
                                       (Prims.of_int (535))
                                       (Prims.of_int (21)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Pure.fst"
                                       (Prims.of_int (536))
                                       (Prims.of_int (2))
                                       (Prims.of_int (542))
                                       (Prims.of_int (47)))))
                              (Obj.magic
                                 (FStar_Tactics_V2_Builtins.log_issues issues))
                              (fun uu___2 ->
                                 (fun uu___2 ->
                                    match res with
                                    | FStar_Pervasives_Native.Some tok ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___3 -> tok)))
                                    | FStar_Pervasives_Native.None ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Pure.fst"
                                                         (Prims.of_int (541))
                                                         (Prims.of_int (10))
                                                         (Prims.of_int (542))
                                                         (Prims.of_int (47)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Pure.fst"
                                                         (Prims.of_int (540))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (542))
                                                         (Prims.of_int (47)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (541))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (542))
                                                               (Prims.of_int (46)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (541))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (542))
                                                               (Prims.of_int (47)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (46)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (46)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (21)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (46)))))
                                                                  (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    t1))
                                                                  (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    t2))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "and")
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___3
                                                                    uu___4))))
                                                                    uu___3)))
                                                            (fun uu___3 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___4
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Could not prove subtyping of ")
                                                                    uu___3))))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              [uu___3]))))
                                                (fun uu___3 ->
                                                   (fun uu___3 ->
                                                      Obj.magic
                                                        (maybe_fail_doc
                                                           issues g
                                                           (Pulse_RuntimeUtils.range_of_term
                                                              t1) uu___3))
                                                     uu___3)))) uu___2)))
                    uu___1))
let (check_equiv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        ((unit, unit, unit) FStar_Tactics_Types.equiv_token
           FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (547)) (Prims.of_int (4))
                   (Prims.of_int (547)) (Prims.of_int (80)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                   (Prims.of_int (545)) (Prims.of_int (25))
                   (Prims.of_int (549)) (Prims.of_int (5)))))
          (Obj.magic
             (Pulse_Typing_Util.check_equiv_now (Pulse_Typing.elab_env g)
                (Pulse_Elaborate_Pure.elab_term t1)
                (Pulse_Elaborate_Pure.elab_term t2)))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | (res, issues) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (548)) (Prims.of_int (2))
                                  (Prims.of_int (548)) (Prims.of_int (21)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                  (Prims.of_int (546)) (Prims.of_int (6))
                                  (Prims.of_int (546)) (Prims.of_int (9)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.log_issues issues))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 -> res)))) uu___)