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
                 (Prims.of_int (13)) (Prims.of_int (28)) (Prims.of_int (13))
                 (Prims.of_int (72)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                 (Prims.of_int (13)) (Prims.of_int (3)) (Prims.of_int (18))
                 (Prims.of_int (40)))))
        (Obj.magic
           (Pulse_Checker_Pure.check_vprop g (Pulse_Syntax_Base.tm_pure p)))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | Prims.Mkdtuple2 (p1, p_typing) ->
                  (match p1.Pulse_Syntax_Base.t with
                   | Pulse_Syntax_Base.Tm_Pure pp ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> Prims.Mkdtuple2 (pp, ()))))
                   | uu___1 ->
                       Obj.magic
                         (Obj.repr
                            (Pulse_Typing_Env.fail g
                               FStar_Pervasives_Native.None "Unexpected prop"))))
             uu___)
let (check_prop_validity :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        ((unit, unit) Pulse_Typing.prop_validity, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p -> fun typing -> Pulse_Checker_Pure.check_prop_validity g p ()
let (check_intro_pure :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Checker_Common.post_hint_opt ->
            ((unit, unit, unit) Pulse_Checker_Common.checker_result_t, 
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                       (Prims.of_int (30)) (Prims.of_int (43))
                       (Prims.of_int (30)) (Prims.of_int (49)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.IntroPure.fst"
                       (Prims.of_int (30)) (Prims.of_int (3))
                       (Prims.of_int (39)) (Prims.of_int (57)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> t.Pulse_Syntax_Base.term1))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | Pulse_Syntax_Base.Tm_IntroPure
                        { Pulse_Syntax_Base.p = p;
                          Pulse_Syntax_Base.should_check = should_check;_}
                        ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.IntroPure.fst"
                                      (Prims.of_int (32)) (Prims.of_int (8))
                                      (Prims.of_int (35)) (Prims.of_int (30)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.IntroPure.fst"
                                      (Prims.of_int (30)) (Prims.of_int (52))
                                      (Prims.of_int (39)) (Prims.of_int (57)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.IntroPure.fst"
                                            (Prims.of_int (32))
                                            (Prims.of_int (11))
                                            (Prims.of_int (32))
                                            (Prims.of_int (32)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.IntroPure.fst"
                                            (Prims.of_int (32))
                                            (Prims.of_int (8))
                                            (Prims.of_int (35))
                                            (Prims.of_int (30)))))
                                   (Obj.magic
                                      (FStar_Tactics_Unseal.unseal
                                         should_check))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         if uu___1
                                         then Obj.magic (check_prop g p)
                                         else
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.IntroPure.fst"
                                                         (Prims.of_int (34))
                                                         (Prims.of_int (24))
                                                         (Prims.of_int (34))
                                                         (Prims.of_int (73)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.IntroPure.fst"
                                                         (Prims.of_int (34))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (35))
                                                         (Prims.of_int (30)))))
                                                (Obj.magic
                                                   (Pulse_Checker_Pure.instantiate_term_implicits
                                                      g p))
                                                (fun uu___3 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        match uu___3 with
                                                        | (p1, uu___5) ->
                                                            Prims.Mkdtuple2
                                                              (p1, ())))))
                                        uu___1)))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   match uu___1 with
                                   | Prims.Mkdtuple2 (p1, p_typing) ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.IntroPure.fst"
                                                     (Prims.of_int (37))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (37))
                                                     (Prims.of_int (45)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.IntroPure.fst"
                                                     (Prims.of_int (37))
                                                     (Prims.of_int (48))
                                                     (Prims.of_int (39))
                                                     (Prims.of_int (57)))))
                                            (Obj.magic
                                               (check_prop_validity g p1 ()))
                                            (fun uu___2 ->
                                               (fun pv ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.IntroPure.fst"
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (20))
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (47)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.IntroPure.fst"
                                                                (Prims.of_int (39))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (39))
                                                                (Prims.of_int (57)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             Pulse_Typing.T_IntroPure
                                                               (g, p1, (),
                                                                 pv)))
                                                       (fun uu___2 ->
                                                          (fun st_typing ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (47)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.IntroPure.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (57)))))
                                                                  (Obj.magic
                                                                    (Pulse_Checker_Common.try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_IntroPure
                                                                    {
                                                                    Pulse_Syntax_Base.p
                                                                    = p1;
                                                                    Pulse_Syntax_Base.should_check
                                                                    =
                                                                    Pulse_Syntax_Base.should_check_true
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_intro_pure
                                                                    p1)
                                                                    st_typing))
                                                                  (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.repack
                                                                    g pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_IntroPure
                                                                    {
                                                                    Pulse_Syntax_Base.p
                                                                    = p1;
                                                                    Pulse_Syntax_Base.should_check
                                                                    =
                                                                    Pulse_Syntax_Base.should_check_true
                                                                    }))
                                                                    uu___2
                                                                    post_hint))
                                                                    uu___2)))
                                                            uu___2))) uu___2)))
                                  uu___1))) uu___)