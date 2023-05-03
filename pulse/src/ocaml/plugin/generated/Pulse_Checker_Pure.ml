open Prims
let (debug :
  (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun msg ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (17))
         (Prims.of_int (5)) (Prims.of_int (17)) (Prims.of_int (18)))
      (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (17))
         (Prims.of_int (2)) (Prims.of_int (18)) (Prims.of_int (22)))
      (Obj.magic (FStar_Tactics_Builtins.debugging ()))
      (fun uu___ ->
         (fun uu___ ->
            if uu___
            then
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (18)) (Prims.of_int (15))
                         (Prims.of_int (18)) (Prims.of_int (22)))
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (18)) (Prims.of_int (7))
                         (Prims.of_int (18)) (Prims.of_int (22)))
                      (Obj.magic (msg ()))
                      (fun uu___1 ->
                         (fun uu___1 ->
                            Obj.magic (FStar_Tactics_Builtins.print uu___1))
                           uu___1)))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
           uu___)
let (rtb_core_check_term :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.typ FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun e ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (21))
           (Prims.of_int (2)) (Prims.of_int (21)) (Prims.of_int (86)))
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (22))
           (Prims.of_int (2)) (Prims.of_int (24)) (Prims.of_int (5)))
        (Obj.magic
           (debug
              (fun uu___ ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (21)) (Prims.of_int (65))
                      (Prims.of_int (21)) (Prims.of_int (85)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                      (Prims.of_int (19)) (Prims.of_int (590))
                      (Prims.of_int (31)))
                   (Obj.magic (FStar_Tactics_Builtins.term_to_string e))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "Calling core_check_term on "
                             (Prims.strcat uu___1 ""))))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (22)) (Prims.of_int (12))
                      (Prims.of_int (22)) (Prims.of_int (43)))
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (23)) (Prims.of_int (2))
                      (Prims.of_int (24)) (Prims.of_int (5)))
                   (Obj.magic
                      (FStar_Tactics_Builtins.core_check_term f e
                         FStar_Tactics_Types.E_Total))
                   (fun uu___1 ->
                      (fun res ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (23)) (Prims.of_int (2))
                                 (Prims.of_int (23)) (Prims.of_int (29)))
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (22)) (Prims.of_int (6))
                                 (Prims.of_int (22)) (Prims.of_int (9)))
                              (Obj.magic
                                 (debug
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 -> "Returned")))
                                         uu___1)))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> res)))) uu___1))) uu___)
let (rtb_tc_term :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.term * FStar_Reflection_Types.typ)
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun e ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (27))
           (Prims.of_int (2)) (Prims.of_int (27)) (Prims.of_int (78)))
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (28))
           (Prims.of_int (2)) (Prims.of_int (30)) (Prims.of_int (5)))
        (Obj.magic
           (debug
              (fun uu___ ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (27)) (Prims.of_int (57))
                      (Prims.of_int (27)) (Prims.of_int (77)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                      (Prims.of_int (19)) (Prims.of_int (590))
                      (Prims.of_int (31)))
                   (Obj.magic (FStar_Tactics_Builtins.term_to_string e))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "Calling tc_term on "
                             (Prims.strcat uu___1 ""))))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (28)) (Prims.of_int (12))
                      (Prims.of_int (28)) (Prims.of_int (35)))
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (29)) (Prims.of_int (2))
                      (Prims.of_int (30)) (Prims.of_int (5)))
                   (Obj.magic
                      (FStar_Tactics_Builtins.tc_term f e
                         FStar_Tactics_Types.E_Total))
                   (fun uu___1 ->
                      (fun res ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (29)) (Prims.of_int (2))
                                 (Prims.of_int (29)) (Prims.of_int (29)))
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (28)) (Prims.of_int (6))
                                 (Prims.of_int (28)) (Prims.of_int (9)))
                              (Obj.magic
                                 (debug
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 -> "Returned")))
                                         uu___1)))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> res)))) uu___1))) uu___)
let (rtb_universe_of :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.universe FStar_Pervasives_Native.option, 
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun e ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (33))
           (Prims.of_int (2)) (Prims.of_int (33)) (Prims.of_int (82)))
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (34))
           (Prims.of_int (2)) (Prims.of_int (36)) (Prims.of_int (5)))
        (Obj.magic
           (debug
              (fun uu___ ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (33)) (Prims.of_int (61))
                      (Prims.of_int (33)) (Prims.of_int (81)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                      (Prims.of_int (19)) (Prims.of_int (590))
                      (Prims.of_int (31)))
                   (Obj.magic (FStar_Tactics_Builtins.term_to_string e))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "Calling universe_of on "
                             (Prims.strcat uu___1 ""))))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (34)) (Prims.of_int (12))
                      (Prims.of_int (34)) (Prims.of_int (31)))
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (35)) (Prims.of_int (2))
                      (Prims.of_int (36)) (Prims.of_int (5)))
                   (Obj.magic (FStar_Tactics_Builtins.universe_of f e))
                   (fun uu___1 ->
                      (fun res ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (35)) (Prims.of_int (2))
                                 (Prims.of_int (35)) (Prims.of_int (29)))
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (34)) (Prims.of_int (6))
                                 (Prims.of_int (34)) (Prims.of_int (9)))
                              (Obj.magic
                                 (debug
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 -> "Returned")))
                                         uu___1)))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> res)))) uu___1))) uu___)
let (rtb_check_subtyping :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        ((unit, unit, unit) FStar_Tactics_Builtins.subtyping_token
           FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (39))
             (Prims.of_int (2)) (Prims.of_int (41)) (Prims.of_int (52)))
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (42))
             (Prims.of_int (2)) (Prims.of_int (44)) (Prims.of_int (5)))
          (Obj.magic
             (debug
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (41)) (Prims.of_int (30))
                        (Prims.of_int (41)) (Prims.of_int (51)))
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (39)) (Prims.of_int (18))
                        (Prims.of_int (41)) (Prims.of_int (51)))
                     (Obj.magic (FStar_Tactics_Builtins.term_to_string t2))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (39)) (Prims.of_int (18))
                                   (Prims.of_int (41)) (Prims.of_int (51)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (39)) (Prims.of_int (18))
                                   (Prims.of_int (41)) (Prims.of_int (51)))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (40))
                                         (Prims.of_int (30))
                                         (Prims.of_int (40))
                                         (Prims.of_int (51)))
                                      (FStar_Range.mk_range
                                         "FStar.Printf.fst"
                                         (Prims.of_int (121))
                                         (Prims.of_int (8))
                                         (Prims.of_int (123))
                                         (Prims.of_int (44)))
                                      (Obj.magic
                                         (FStar_Tactics_Builtins.term_to_string
                                            t1))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 ->
                                              fun x ->
                                                Prims.strcat
                                                  (Prims.strcat
                                                     "Calling check_subtyping on "
                                                     (Prims.strcat uu___2
                                                        " <: "))
                                                  (Prims.strcat x "")))))
                                (fun uu___2 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> uu___2 uu___1)))) uu___1))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (42)) (Prims.of_int (12))
                        (Prims.of_int (42)) (Prims.of_int (39)))
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (43)) (Prims.of_int (2))
                        (Prims.of_int (44)) (Prims.of_int (5)))
                     (Obj.magic
                        (FStar_Tactics_Builtins.check_subtyping f t1 t2))
                     (fun uu___1 ->
                        (fun res ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (43)) (Prims.of_int (2))
                                   (Prims.of_int (43)) (Prims.of_int (29)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (42)) (Prims.of_int (6))
                                   (Prims.of_int (42)) (Prims.of_int (9)))
                                (Obj.magic
                                   (debug
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 -> "Returned")))
                                           uu___1)))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> res)))) uu___1))) uu___)
let (rtb_instantiate_implicits :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.term * FStar_Reflection_Types.typ)
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (47))
           (Prims.of_int (2)) (Prims.of_int (48)) (Prims.of_int (51)))
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (49))
           (Prims.of_int (2)) (Prims.of_int (51)) (Prims.of_int (5)))
        (Obj.magic
           (debug
              (fun uu___ ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (48)) (Prims.of_int (30))
                      (Prims.of_int (48)) (Prims.of_int (50)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                      (Prims.of_int (19)) (Prims.of_int (590))
                      (Prims.of_int (31)))
                   (Obj.magic (FStar_Tactics_Builtins.term_to_string t))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "Calling elab_term on "
                             (Prims.strcat uu___1 ""))))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (49)) (Prims.of_int (12))
                      (Prims.of_int (49)) (Prims.of_int (41)))
                   (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                      (Prims.of_int (50)) (Prims.of_int (2))
                      (Prims.of_int (51)) (Prims.of_int (5)))
                   (Obj.magic
                      (FStar_Tactics_Builtins.instantiate_implicits f t))
                   (fun uu___1 ->
                      (fun res ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (50)) (Prims.of_int (2))
                                 (Prims.of_int (50)) (Prims.of_int (29)))
                              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                                 (Prims.of_int (49)) (Prims.of_int (6))
                                 (Prims.of_int (49)) (Prims.of_int (9)))
                              (Obj.magic
                                 (debug
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 -> "Returned")))
                                         uu___1)))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> res)))) uu___1))) uu___)
let catch_all :
  'a .
    (unit ->
       ('a FStar_Pervasives_Native.option, unit)
         FStar_Tactics_Effect.tac_repr)
      ->
      ('a FStar_Pervasives_Native.option, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (55))
         (Prims.of_int (10)) (Prims.of_int (55)) (Prims.of_int (19)))
      (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (55))
         (Prims.of_int (4)) (Prims.of_int (57)) (Prims.of_int (16)))
      (Obj.magic (FStar_Tactics_Builtins.catch f))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | FStar_Pervasives.Inl exn -> FStar_Pervasives_Native.None
              | FStar_Pervasives.Inr v -> v))
let (check_universe :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.term ->
        ((Pulse_Syntax.universe, unit) Prims.dtuple2, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun f0 ->
    fun g ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (61))
             (Prims.of_int (12)) (Prims.of_int (61)) (Prims.of_int (29)))
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (62))
             (Prims.of_int (4)) (Prims.of_int (76)) (Prims.of_int (34)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Typing.extend_env_l f0 g))
          (fun uu___ ->
             (fun f ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (62)) (Prims.of_int (13))
                        (Prims.of_int (62)) (Prims.of_int (24)))
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (63)) (Prims.of_int (4))
                        (Prims.of_int (76)) (Prims.of_int (34)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                     (fun uu___ ->
                        (fun rt ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (63)) (Prims.of_int (17))
                                   (Prims.of_int (63)) (Prims.of_int (58)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (64)) (Prims.of_int (4))
                                   (Prims.of_int (76)) (Prims.of_int (34)))
                                (Obj.magic
                                   (catch_all
                                      (fun uu___ -> rtb_universe_of f rt)))
                                (fun uu___ ->
                                   (fun ru_opt ->
                                      match ru_opt with
                                      | FStar_Pervasives_Native.None ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (65))
                                                  (Prims.of_int (21))
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (47)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (65))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (47)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (67))
                                                        (Prims.of_int (25))
                                                        (Prims.of_int (67))
                                                        (Prims.of_int (46)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (65))
                                                        (Prims.of_int (21))
                                                        (Prims.of_int (67))
                                                        (Prims.of_int (47)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Builtins.term_to_string
                                                           rt))
                                                     (fun uu___ ->
                                                        (fun uu___ ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (65))
                                                                   (Prims.of_int (21))
                                                                   (Prims.of_int (67))
                                                                   (Prims.of_int (47)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (65))
                                                                   (Prims.of_int (21))
                                                                   (Prims.of_int (67))
                                                                   (Prims.of_int (47)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    t))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    ""
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    " elaborated to "))
                                                                    (Prims.strcat
                                                                    x
                                                                    "; Not typable as a universe")))))
                                                                (fun uu___1
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    uu___1
                                                                    uu___))))
                                                          uu___)))
                                               (fun uu___ ->
                                                  FStar_Tactics_Derived.fail
                                                    uu___))
                                      | FStar_Pervasives_Native.Some ru ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (69))
                                                  (Prims.of_int (17))
                                                  (Prims.of_int (69))
                                                  (Prims.of_int (37)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (73))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (76))
                                                  (Prims.of_int (34)))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___ ->
                                                     Pulse_Readback.readback_universe
                                                       ru))
                                               (fun uu___ ->
                                                  (fun uopt ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (73))
                                                             (Prims.of_int (71))
                                                             (Prims.of_int (73))
                                                             (Prims.of_int (93)))
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (74))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (76))
                                                             (Prims.of_int (34)))
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___ ->
                                                                FStar_Reflection_Typing.T_Token
                                                                  (f, rt,
                                                                    (FStar_Tactics_Types.E_Total,
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Type
                                                                    ru))),
                                                                    ())))
                                                          (fun proof ->
                                                             match uopt with
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 FStar_Tactics_Derived.fail
                                                                   "check_universe: failed to readback the universe"
                                                             | FStar_Pervasives_Native.Some
                                                                 u ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun uu___
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (u, ())))))
                                                    uu___))) uu___))) uu___)))
               uu___)
let (tc_meta_callback :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.term, FStar_Reflection_Types.term,
         (unit, unit, unit) FStar_Reflection_Typing.tot_typing)
         FStar_Pervasives.dtuple3 FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun e ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (82))
           (Prims.of_int (6)) (Prims.of_int (85)) (Prims.of_int (68)))
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (81))
           (Prims.of_int (8)) (Prims.of_int (81)) (Prims.of_int (11)))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (82)) (Prims.of_int (12)) (Prims.of_int (82))
                 (Prims.of_int (48)))
              (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                 (Prims.of_int (82)) (Prims.of_int (6)) (Prims.of_int (85))
                 (Prims.of_int (68)))
              (Obj.magic (catch_all (fun uu___ -> rtb_tc_term f e)))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      match uu___ with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (e1, t) ->
                          FStar_Pervasives_Native.Some
                            (FStar_Pervasives.Mkdtuple3
                               (e1, t,
                                 (FStar_Reflection_Typing.T_Token
                                    (f, e1, (FStar_Tactics_Types.E_Total, t),
                                      ()))))))))
        (fun res -> FStar_Tactics_Effect.lift_div_tac (fun uu___ -> res))
let (check_tot_univ :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.term ->
        ((Pulse_Syntax.term, Pulse_Syntax.universe, Pulse_Syntax.term, 
           unit, (unit, unit, unit, unit) Pulse_Typing.typing)
           FStar_Pervasives.dtuple5,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (95))
             (Prims.of_int (13)) (Prims.of_int (95)) (Prims.of_int (29)))
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (96))
             (Prims.of_int (4)) (Prims.of_int (109)) (Prims.of_int (32)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Typing.extend_env_l f g))
          (fun uu___ ->
             (fun fg ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (96)) (Prims.of_int (13))
                        (Prims.of_int (96)) (Prims.of_int (24)))
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (97)) (Prims.of_int (4))
                        (Prims.of_int (109)) (Prims.of_int (32)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                     (fun uu___ ->
                        (fun rt ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (97)) (Prims.of_int (10))
                                   (Prims.of_int (97)) (Prims.of_int (32)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (97)) (Prims.of_int (4))
                                   (Prims.of_int (109)) (Prims.of_int (32)))
                                (Obj.magic (tc_meta_callback fg rt))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      match uu___ with
                                      | FStar_Pervasives_Native.None ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (100))
                                                  (Prims.of_int (10))
                                                  (Prims.of_int (102))
                                                  (Prims.of_int (48)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (99))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (102))
                                                  (Prims.of_int (48)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (102))
                                                        (Prims.of_int (26))
                                                        (Prims.of_int (102))
                                                        (Prims.of_int (47)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (100))
                                                        (Prims.of_int (10))
                                                        (Prims.of_int (102))
                                                        (Prims.of_int (48)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Builtins.term_to_string
                                                           rt))
                                                     (fun uu___1 ->
                                                        (fun uu___1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (100))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (102))
                                                                   (Prims.of_int (48)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (100))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (102))
                                                                   (Prims.of_int (48)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    t))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_tot_univ: "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " elaborated to "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " Not typeable")))))
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                          uu___1)))
                                               (fun uu___1 ->
                                                  FStar_Tactics_Derived.fail
                                                    uu___1))
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Pervasives.Mkdtuple3
                                          (rt1, ty', tok)) ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (104))
                                                  (Prims.of_int (12))
                                                  (Prims.of_int (104))
                                                  (Prims.of_int (43)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (104))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (109))
                                                  (Prims.of_int (32)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (104))
                                                        (Prims.of_int (12))
                                                        (Prims.of_int (104))
                                                        (Prims.of_int (26)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (104))
                                                        (Prims.of_int (12))
                                                        (Prims.of_int (104))
                                                        (Prims.of_int (43)))
                                                     (Obj.magic
                                                        (Pulse_Readback.readback_ty
                                                           rt1))
                                                     (fun uu___1 ->
                                                        (fun uu___1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (104))
                                                                   (Prims.of_int (28))
                                                                   (Prims.of_int (104))
                                                                   (Prims.of_int (43)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (104))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (104))
                                                                   (Prims.of_int (43)))
                                                                (Obj.magic
                                                                   (Pulse_Readback.readback_ty
                                                                    ty'))
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (uu___1,
                                                                    uu___2)))))
                                                          uu___1)))
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     match uu___1 with
                                                     | (FStar_Pervasives_Native.None,
                                                        uu___2) ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Derived.fail
                                                                 "Inexpressible type/term"))
                                                     | (uu___2,
                                                        FStar_Pervasives_Native.None)
                                                         ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Derived.fail
                                                                 "Inexpressible type/term"))
                                                     | (FStar_Pervasives_Native.Some
                                                        t1,
                                                        FStar_Pervasives_Native.Some
                                                        ty) ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (48)))
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (32)))
                                                                 (Obj.magic
                                                                    (
                                                                    check_universe
                                                                    f g ty))
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u, uty)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (t1, u,
                                                                    ty, (),
                                                                    tok))))))
                                                    uu___1))) uu___))) uu___)))
               uu___)
let (check_tot :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.term ->
        ((Pulse_Syntax.term, Pulse_Syntax.term,
           (unit, unit, unit, unit) Pulse_Typing.typing)
           FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (115))
             (Prims.of_int (13)) (Prims.of_int (115)) (Prims.of_int (29)))
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (116))
             (Prims.of_int (4)) (Prims.of_int (131)) (Prims.of_int (24)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Typing.extend_env_l f g))
          (fun uu___ ->
             (fun fg ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (116)) (Prims.of_int (13))
                        (Prims.of_int (116)) (Prims.of_int (24)))
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (117)) (Prims.of_int (4))
                        (Prims.of_int (131)) (Prims.of_int (24)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                     (fun uu___ ->
                        (fun rt ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (117)) (Prims.of_int (4))
                                   (Prims.of_int (119)) (Prims.of_int (34)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (120)) (Prims.of_int (4))
                                   (Prims.of_int (131)) (Prims.of_int (24)))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (117))
                                         (Prims.of_int (12))
                                         (Prims.of_int (119))
                                         (Prims.of_int (34)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (117))
                                         (Prims.of_int (4))
                                         (Prims.of_int (119))
                                         (Prims.of_int (34)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (119))
                                               (Prims.of_int (12))
                                               (Prims.of_int (119))
                                               (Prims.of_int (33)))
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Pure.fst"
                                               (Prims.of_int (117))
                                               (Prims.of_int (12))
                                               (Prims.of_int (119))
                                               (Prims.of_int (34)))
                                            (Obj.magic
                                               (FStar_Tactics_Builtins.term_to_string
                                                  rt))
                                            (fun uu___ ->
                                               (fun uu___ ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (117))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (119))
                                                          (Prims.of_int (34)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Pure.fst"
                                                          (Prims.of_int (117))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (119))
                                                          (Prims.of_int (34)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Pure.fst"
                                                                (Prims.of_int (118))
                                                                (Prims.of_int (12))
                                                                (Prims.of_int (118))
                                                                (Prims.of_int (32)))
                                                             (FStar_Range.mk_range
                                                                "FStar.Printf.fst"
                                                                (Prims.of_int (121))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (123))
                                                                (Prims.of_int (44)))
                                                             (Obj.magic
                                                                (Pulse_Syntax_Printer.term_to_string
                                                                   t))
                                                             (fun uu___1 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___2
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_tot : called on "
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    " elaborated to "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               uu___1 uu___))))
                                                 uu___)))
                                      (fun uu___ ->
                                         (fun uu___ ->
                                            Obj.magic
                                              (FStar_Tactics_Builtins.print
                                                 uu___)) uu___)))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Pure.fst"
                                              (Prims.of_int (120))
                                              (Prims.of_int (10))
                                              (Prims.of_int (120))
                                              (Prims.of_int (32)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Pure.fst"
                                              (Prims.of_int (120))
                                              (Prims.of_int (4))
                                              (Prims.of_int (131))
                                              (Prims.of_int (24)))
                                           (Obj.magic
                                              (tc_meta_callback fg rt))
                                           (fun uu___1 ->
                                              (fun uu___1 ->
                                                 match uu___1 with
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (123))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (125))
                                                             (Prims.of_int (34)))
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (122))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (125))
                                                             (Prims.of_int (34)))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (125))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (125))
                                                                   (Prims.of_int (33)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (123))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (125))
                                                                   (Prims.of_int (34)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Builtins.term_to_string
                                                                    rt))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (32)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    t))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_tot : "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " elaborated to "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " Not typeable")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                          (fun uu___2 ->
                                                             FStar_Tactics_Derived.fail
                                                               uu___2))
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Pervasives.Mkdtuple3
                                                     (rt1, ty', tok)) ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (127))
                                                             (Prims.of_int (12))
                                                             (Prims.of_int (127))
                                                             (Prims.of_int (43)))
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (127))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (131))
                                                             (Prims.of_int (24)))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (127))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (127))
                                                                   (Prims.of_int (26)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (127))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (127))
                                                                   (Prims.of_int (43)))
                                                                (Obj.magic
                                                                   (Pulse_Readback.readback_ty
                                                                    rt1))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (43)))
                                                                    (Obj.magic
                                                                    (Pulse_Readback.readback_ty
                                                                    ty'))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (uu___2,
                                                                    uu___3)))))
                                                                    uu___2)))
                                                          (fun uu___2 ->
                                                             match uu___2
                                                             with
                                                             | (FStar_Pervasives_Native.None,
                                                                uu___3) ->
                                                                 FStar_Tactics_Derived.fail
                                                                   "Inexpressible type/term"
                                                             | (uu___3,
                                                                FStar_Pervasives_Native.None)
                                                                 ->
                                                                 FStar_Tactics_Derived.fail
                                                                   "Inexpressible type/term"
                                                             | (FStar_Pervasives_Native.Some
                                                                t1,
                                                                FStar_Pervasives_Native.Some
                                                                ty) ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t1, ty,
                                                                    tok)))))
                                                uu___1))) uu___))) uu___)))
               uu___)
let (tc_expected_meta_callback :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        ((FStar_Reflection_Types.term,
           (unit, unit, unit) FStar_Reflection_Typing.tot_typing)
           Prims.dtuple2 FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun e ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (135))
             (Prims.of_int (15)) (Prims.of_int (135)) (Prims.of_int (51)))
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (136))
             (Prims.of_int (4)) (Prims.of_int (147)) (Prims.of_int (86)))
          (Obj.magic (catch_all (fun uu___ -> rtb_tc_term f e)))
          (fun uu___ ->
             (fun ropt ->
                match ropt with
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> FStar_Pervasives_Native.None)))
                | FStar_Pervasives_Native.Some (e1, te) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                               (Prims.of_int (140)) (Prims.of_int (12))
                               (Prims.of_int (140)) (Prims.of_int (59)))
                            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                               (Prims.of_int (140)) (Prims.of_int (6))
                               (Prims.of_int (147)) (Prims.of_int (86)))
                            (Obj.magic
                               (catch_all
                                  (fun uu___ -> rtb_check_subtyping f te t)))
                            (fun uu___ ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    match uu___ with
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Pervasives_Native.None
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Pervasives_Native.Some
                                          (Prims.Mkdtuple2
                                             (e1,
                                               (FStar_Reflection_Typing.T_Sub
                                                  (f, e1,
                                                    (FStar_Tactics_Types.E_Total,
                                                      te),
                                                    (FStar_Tactics_Types.E_Total,
                                                      t),
                                                    (FStar_Reflection_Typing.T_Token
                                                       (f, e1,
                                                         (FStar_Tactics_Types.E_Total,
                                                           te), ())),
                                                    (FStar_Reflection_Typing.Relc_typ
                                                       (f, te, t,
                                                         FStar_Tactics_Types.E_Total,
                                                         FStar_Reflection_Typing.R_Sub,
                                                         (FStar_Reflection_Typing.Rel_subtyping_token
                                                            (f, te, t, ())))))))))))))
               uu___)
let (check_tot_with_expected_typ :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.term ->
        Pulse_Syntax.term ->
          ((Pulse_Syntax.term, (unit, unit, unit, unit) Pulse_Typing.typing)
             Prims.dtuple2,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun e ->
        fun t ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (151)) (Prims.of_int (13)) (Prims.of_int (151))
               (Prims.of_int (29)))
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (152)) (Prims.of_int (4)) (Prims.of_int (161))
               (Prims.of_int (42)))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_Typing.extend_env_l f g))
            (fun uu___ ->
               (fun fg ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                          (Prims.of_int (152)) (Prims.of_int (13))
                          (Prims.of_int (152)) (Prims.of_int (24)))
                       (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                          (Prims.of_int (153)) (Prims.of_int (4))
                          (Prims.of_int (161)) (Prims.of_int (42)))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ -> Pulse_Elaborate_Pure.elab_term e))
                       (fun uu___ ->
                          (fun re ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Pure.fst"
                                     (Prims.of_int (153)) (Prims.of_int (13))
                                     (Prims.of_int (153)) (Prims.of_int (24)))
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Pure.fst"
                                     (Prims.of_int (154)) (Prims.of_int (4))
                                     (Prims.of_int (161)) (Prims.of_int (42)))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ ->
                                        Pulse_Elaborate_Pure.elab_term t))
                                  (fun uu___ ->
                                     (fun rt ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Pure.fst"
                                                (Prims.of_int (154))
                                                (Prims.of_int (10))
                                                (Prims.of_int (154))
                                                (Prims.of_int (44)))
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Pure.fst"
                                                (Prims.of_int (154))
                                                (Prims.of_int (4))
                                                (Prims.of_int (161))
                                                (Prims.of_int (42)))
                                             (Obj.magic
                                                (tc_expected_meta_callback fg
                                                   re rt))
                                             (fun uu___ ->
                                                (fun uu___ ->
                                                   match uu___ with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (155))
                                                               (Prims.of_int (21))
                                                               (Prims.of_int (157))
                                                               (Prims.of_int (76)))
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (155))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (157))
                                                               (Prims.of_int (76)))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (75)))
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (76)))
                                                                  (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    t))
                                                                  (fun uu___1
                                                                    ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (75)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    e))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_tot_with_expected_typ: "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " not typeable at "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                                    uu___1)))
                                                            (fun uu___1 ->
                                                               FStar_Tactics_Derived.fail
                                                                 uu___1))
                                                   | FStar_Pervasives_Native.Some
                                                       (Prims.Mkdtuple2
                                                       (re1, tok)) ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (159))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (159))
                                                               (Prims.of_int (28)))
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Pure.fst"
                                                               (Prims.of_int (159))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (161))
                                                               (Prims.of_int (42)))
                                                            (Obj.magic
                                                               (Pulse_Readback.readback_ty
                                                                  re1))
                                                            (fun uu___1 ->
                                                               match uu___1
                                                               with
                                                               | FStar_Pervasives_Native.Some
                                                                   e1 ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.Mkdtuple2
                                                                    (e1, tok))
                                                               | FStar_Pervasives_Native.None
                                                                   ->
                                                                   FStar_Tactics_Derived.fail
                                                                    "readback failed")))
                                                  uu___))) uu___))) uu___)))
                 uu___)
let (tc_with_core :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.term,
         (unit, unit, unit) FStar_Reflection_Typing.tot_typing) Prims.dtuple2
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun e ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (165))
           (Prims.of_int (15)) (Prims.of_int (165)) (Prims.of_int (59)))
        (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (166))
           (Prims.of_int (4)) (Prims.of_int (169)) (Prims.of_int (63)))
        (Obj.magic (catch_all (fun uu___ -> rtb_core_check_term f e)))
        (fun ropt ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                match ropt with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some t ->
                    FStar_Pervasives_Native.Some
                      (Prims.Mkdtuple2
                         (t,
                           (FStar_Reflection_Typing.T_Token
                              (f, e, (FStar_Tactics_Types.E_Total, t), ()))))))
let (check_with_core :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.term ->
        ((Pulse_Syntax.term, (unit, unit, unit, unit) Pulse_Typing.typing)
           Prims.dtuple2,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (174))
             (Prims.of_int (13)) (Prims.of_int (174)) (Prims.of_int (29)))
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (175))
             (Prims.of_int (4)) (Prims.of_int (188)) (Prims.of_int (23)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Typing.extend_env_l f g))
          (fun uu___ ->
             (fun fg ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (175)) (Prims.of_int (13))
                        (Prims.of_int (175)) (Prims.of_int (24)))
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (176)) (Prims.of_int (4))
                        (Prims.of_int (188)) (Prims.of_int (23)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                     (fun uu___ ->
                        (fun rt ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (176)) (Prims.of_int (10))
                                   (Prims.of_int (176)) (Prims.of_int (28)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (176)) (Prims.of_int (4))
                                   (Prims.of_int (188)) (Prims.of_int (23)))
                                (Obj.magic (tc_with_core fg rt))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      match uu___ with
                                      | FStar_Pervasives_Native.None ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (179))
                                                  (Prims.of_int (10))
                                                  (Prims.of_int (181))
                                                  (Prims.of_int (34)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (178))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (181))
                                                  (Prims.of_int (34)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (181))
                                                        (Prims.of_int (12))
                                                        (Prims.of_int (181))
                                                        (Prims.of_int (33)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (179))
                                                        (Prims.of_int (10))
                                                        (Prims.of_int (181))
                                                        (Prims.of_int (34)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Builtins.term_to_string
                                                           rt))
                                                     (fun uu___1 ->
                                                        (fun uu___1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (179))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (181))
                                                                   (Prims.of_int (34)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (179))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (181))
                                                                   (Prims.of_int (34)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (32)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    t))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_tot: "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " elaborated to "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " Not typeable")))))
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                          uu___1)))
                                               (fun uu___1 ->
                                                  FStar_Tactics_Derived.fail
                                                    uu___1))
                                      | FStar_Pervasives_Native.Some
                                          (Prims.Mkdtuple2 (ty', tok)) ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (183))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (183))
                                                  (Prims.of_int (29)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (183))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (188))
                                                  (Prims.of_int (23)))
                                               (Obj.magic
                                                  (Pulse_Readback.readback_ty
                                                     ty'))
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     match uu___1 with
                                                     | FStar_Pervasives_Native.None
                                                         ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (61)))
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (61)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    t))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    ty'))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Inexpressible type "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " for term "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___2)))
                                                     | FStar_Pervasives_Native.Some
                                                         ty ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___2
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (ty, tok)))))
                                                    uu___1))) uu___))) uu___)))
               uu___)
let (check_vprop :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.term ->
        ((Pulse_Syntax.term, unit) Prims.dtuple2, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (194))
             (Prims.of_int (25)) (Prims.of_int (194)) (Prims.of_int (40)))
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (194))
             (Prims.of_int (4)) (Prims.of_int (197)) (Prims.of_int (36)))
          (Obj.magic (check_tot f g t))
          (fun uu___ ->
             match uu___ with
             | FStar_Pervasives.Mkdtuple3 (t1, ty, d) ->
                 (match ty with
                  | Pulse_Syntax.Tm_VProp ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.Mkdtuple2 (t1, ()))
                  | uu___1 -> FStar_Tactics_Derived.fail "Expected a vprop"))
let (check_vprop_with_core :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (203))
             (Prims.of_int (22)) (Prims.of_int (203)) (Prims.of_int (43)))
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (203))
             (Prims.of_int (4)) (Prims.of_int (206)) (Prims.of_int (36)))
          (Obj.magic (check_with_core f g t))
          (fun uu___ ->
             match uu___ with
             | Prims.Mkdtuple2 (ty, d) ->
                 (match ty with
                  | Pulse_Syntax.Tm_VProp ->
                      FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ())
                  | uu___1 -> FStar_Tactics_Derived.fail "Expected a vprop"))
let (get_non_informative_witness :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.universe ->
        Pulse_Syntax.term ->
          ((unit, unit, unit, unit) Pulse_Typing.non_informative_t, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun u ->
        fun t ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (211)) (Prims.of_int (8)) (Prims.of_int (212))
               (Prims.of_int (52)))
            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
               (Prims.of_int (213)) (Prims.of_int (4)) (Prims.of_int (233))
               (Prims.of_int (16)))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  fun uu___1 ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (211)) (Prims.of_int (15))
                         (Prims.of_int (212)) (Prims.of_int (52)))
                      (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                         (Prims.of_int (211)) (Prims.of_int (8))
                         (Prims.of_int (212)) (Prims.of_int (52)))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                               (Prims.of_int (212)) (Prims.of_int (31))
                               (Prims.of_int (212)) (Prims.of_int (51)))
                            (FStar_Range.mk_range "prims.fst"
                               (Prims.of_int (590)) (Prims.of_int (19))
                               (Prims.of_int (590)) (Prims.of_int (31)))
                            (Obj.magic
                               (Pulse_Syntax_Printer.term_to_string t))
                            (fun uu___2 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___3 ->
                                    Prims.strcat
                                      "non_informative_witness not supported for "
                                      (Prims.strcat uu___2 "")))))
                      (fun uu___2 -> FStar_Tactics_Derived.fail uu___2)))
            (fun uu___ ->
               (fun err ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                          (Prims.of_int (214)) (Prims.of_int (6))
                          (Prims.of_int (227)) (Prims.of_int (17)))
                       (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                          (Prims.of_int (229)) (Prims.of_int (4))
                          (Prims.of_int (233)) (Prims.of_int (16)))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             match t with
                             | Pulse_Syntax.Tm_FVar l ->
                                 if l = FStar_Reflection_Const.unit_lid
                                 then
                                   FStar_Pervasives_Native.Some
                                     (Pulse_Syntax.Tm_FVar
                                        (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                           "unit_non_informative"))
                                 else
                                   if l = FStar_Reflection_Const.prop_qn
                                   then
                                     FStar_Pervasives_Native.Some
                                       (Pulse_Syntax.Tm_FVar
                                          (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                             "prop_non_informative"))
                                   else FStar_Pervasives_Native.None
                             | Pulse_Syntax.Tm_PureApp
                                 (Pulse_Syntax.Tm_UInst (l, u'::[]),
                                  FStar_Pervasives_Native.None, arg)
                                 ->
                                 if l = FStar_Reflection_Const.squash_qn
                                 then
                                   FStar_Pervasives_Native.Some
                                     (Pulse_Syntax.Tm_PureApp
                                        ((Pulse_Syntax.Tm_UInst
                                            ((Pulse_Reflection_Util.mk_steel_wrapper_lid
                                                "squash_non_informative"),
                                              [u'])),
                                          FStar_Pervasives_Native.None, arg))
                                 else
                                   if l = Pulse_Reflection_Util.erased_lid
                                   then
                                     FStar_Pervasives_Native.Some
                                       (Pulse_Syntax.Tm_PureApp
                                          ((Pulse_Syntax.Tm_UInst
                                              ((Pulse_Reflection_Util.mk_steel_wrapper_lid
                                                  "erased_non_informative"),
                                                [u'])),
                                            FStar_Pervasives_Native.None,
                                            arg))
                                   else FStar_Pervasives_Native.None
                             | uu___1 -> FStar_Pervasives_Native.None))
                       (fun uu___ ->
                          (fun eopt ->
                             match eopt with
                             | FStar_Pervasives_Native.None ->
                                 Obj.magic (err ())
                             | FStar_Pervasives_Native.Some e ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (232))
                                         (Prims.of_int (23))
                                         (Prims.of_int (232))
                                         (Prims.of_int (88)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Pure.fst"
                                         (Prims.of_int (232))
                                         (Prims.of_int (6))
                                         (Prims.of_int (233))
                                         (Prims.of_int (16)))
                                      (Obj.magic
                                         (check_tot_with_expected_typ f g e
                                            (Pulse_Typing.non_informative_witness_t
                                               u t)))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              match uu___ with
                                              | Prims.Mkdtuple2 (x, y) ->
                                                  Prims.Mkdtuple2 (x, ())))))
                            uu___))) uu___)
let (instantiate_implicits :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Typing.env ->
      Pulse_Syntax.term ->
        ((Pulse_Syntax.term * Pulse_Syntax.term), unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun g ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (236))
             (Prims.of_int (10)) (Prims.of_int (236)) (Prims.of_int (26)))
          (FStar_Range.mk_range "Pulse.Checker.Pure.fst" (Prims.of_int (237))
             (Prims.of_int (2)) (Prims.of_int (248)) (Prims.of_int (84)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Typing.extend_env_l f g))
          (fun uu___ ->
             (fun f1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (237)) (Prims.of_int (11))
                        (Prims.of_int (237)) (Prims.of_int (22)))
                     (FStar_Range.mk_range "Pulse.Checker.Pure.fst"
                        (Prims.of_int (238)) (Prims.of_int (2))
                        (Prims.of_int (248)) (Prims.of_int (84)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
                     (fun uu___ ->
                        (fun rt ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (238)) (Prims.of_int (13))
                                   (Prims.of_int (238)) (Prims.of_int (64)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Pure.fst"
                                   (Prims.of_int (239)) (Prims.of_int (2))
                                   (Prims.of_int (248)) (Prims.of_int (84)))
                                (Obj.magic
                                   (catch_all
                                      (fun uu___ ->
                                         rtb_instantiate_implicits f1 rt)))
                                (fun uu___ ->
                                   (fun topt ->
                                      match topt with
                                      | FStar_Pervasives_Native.None ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (240))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (242))
                                                  (Prims.of_int (45)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (240))
                                                  (Prims.of_int (12))
                                                  (Prims.of_int (242))
                                                  (Prims.of_int (45)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (242))
                                                        (Prims.of_int (23))
                                                        (Prims.of_int (242))
                                                        (Prims.of_int (44)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Pure.fst"
                                                        (Prims.of_int (240))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (242))
                                                        (Prims.of_int (45)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Builtins.term_to_string
                                                           rt))
                                                     (fun uu___ ->
                                                        (fun uu___ ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (240))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (242))
                                                                   (Prims.of_int (45)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Pure.fst"
                                                                   (Prims.of_int (240))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (242))
                                                                   (Prims.of_int (45)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Pure.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    t))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    ""
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    " elaborated to "))
                                                                    (Prims.strcat
                                                                    x
                                                                    "; Could not instantiate implicits")))))
                                                                (fun uu___1
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    uu___1
                                                                    uu___))))
                                                          uu___)))
                                               (fun uu___ ->
                                                  FStar_Tactics_Derived.fail
                                                    uu___))
                                      | FStar_Pervasives_Native.Some 
                                          (t1, ty) ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (244))
                                                  (Prims.of_int (15))
                                                  (Prims.of_int (244))
                                                  (Prims.of_int (28)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Pure.fst"
                                                  (Prims.of_int (245))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (248))
                                                  (Prims.of_int (84)))
                                               (Obj.magic
                                                  (Pulse_Readback.readback_ty
                                                     t1))
                                               (fun uu___ ->
                                                  (fun topt1 ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (245))
                                                             (Prims.of_int (16))
                                                             (Prims.of_int (245))
                                                             (Prims.of_int (30)))
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Pure.fst"
                                                             (Prims.of_int (246))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (248))
                                                             (Prims.of_int (84)))
                                                          (Obj.magic
                                                             (Pulse_Readback.readback_ty
                                                                ty))
                                                          (fun tyopt ->
                                                             match (topt1,
                                                                    tyopt)
                                                             with
                                                             | (FStar_Pervasives_Native.Some
                                                                t2,
                                                                FStar_Pervasives_Native.Some
                                                                ty1) ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun uu___
                                                                    ->
                                                                    (t2, ty1))
                                                             | uu___ ->
                                                                 FStar_Tactics_Derived.fail
                                                                   "instantiate_implicits: could not readback the resulting term/typ")))
                                                    uu___))) uu___))) uu___)))
               uu___)