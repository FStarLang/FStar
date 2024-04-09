open Prims
let (check_vprop_equiv_ext :
  Pulse_Syntax_Base.range ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun r ->
    fun g ->
      fun p ->
        fun q ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Rewrite.fst"
                     (Prims.of_int (30)) (Prims.of_int (20))
                     (Prims.of_int (30)) (Prims.of_int (50)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Rewrite.fst"
                     (Prims.of_int (30)) Prims.int_one (Prims.of_int (39))
                     (Prims.of_int (22)))))
            (Obj.magic
               (FStar_Tactics_V2_Builtins.check_equiv
                  (Pulse_Typing.elab_env g) p q))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | (res, issues) ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Rewrite.fst"
                                    (Prims.of_int (31)) (Prims.of_int (2))
                                    (Prims.of_int (31)) (Prims.of_int (21)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Rewrite.fst"
                                    (Prims.of_int (32)) (Prims.of_int (2))
                                    (Prims.of_int (39)) (Prims.of_int (22)))))
                           (Obj.magic
                              (FStar_Tactics_V2_Builtins.log_issues issues))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 match res with
                                 | FStar_Pervasives_Native.None ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Rewrite.fst"
                                                      (Prims.of_int (35))
                                                      (Prims.of_int (11))
                                                      (Prims.of_int (37))
                                                      (Prims.of_int (17)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Rewrite.fst"
                                                      (Prims.of_int (34))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (37))
                                                      (Prims.of_int (17)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Rewrite.fst"
                                                            (Prims.of_int (35))
                                                            (Prims.of_int (11))
                                                            (Prims.of_int (37))
                                                            (Prims.of_int (17)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Rewrite.fst"
                                                            (Prims.of_int (35))
                                                            (Prims.of_int (11))
                                                            (Prims.of_int (37))
                                                            (Prims.of_int (17)))))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Rewrite.fst"
                                                                  (Prims.of_int (36))
                                                                  (Prims.of_int (12))
                                                                  (Prims.of_int (36))
                                                                  (Prims.of_int (16)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Rewrite.fst"
                                                                  (Prims.of_int (35))
                                                                  (Prims.of_int (11))
                                                                  (Prims.of_int (37))
                                                                  (Prims.of_int (17)))))
                                                         (Obj.magic
                                                            (Pulse_PP.pp
                                                               Pulse_PP.printable_fstar_term
                                                               p))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (17)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (17)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    q))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    [uu___3]))))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___2 ::
                                                                    uu___3))))
                                                              uu___2)))
                                                   (fun uu___2 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 ->
                                                           (Pulse_PP.text
                                                              "rewrite: could not prove equality of")
                                                           :: uu___2))))
                                             (fun uu___2 ->
                                                (fun uu___2 ->
                                                   Obj.magic
                                                     (Pulse_Typing_Env.fail_doc
                                                        g
                                                        (FStar_Pervasives_Native.Some
                                                           r) uu___2)) uu___2)))
                                 | FStar_Pervasives_Native.Some token ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 -> ())))) uu___1)))
                 uu___)
let rec (check_vprop_equiv :
  Pulse_Syntax_Base.range ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun r ->
             fun g ->
               fun p ->
                 fun q ->
                   if Pulse_Syntax_Base.eq_tm p q
                   then
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___ -> ())))
                   else
                     Obj.magic
                       (Obj.repr
                          (match ((Pulse_Syntax_Pure.inspect_term p),
                                   (Pulse_Syntax_Pure.inspect_term q))
                           with
                           | (Pulse_Syntax_Pure.Tm_ForallSL (u1, b1, t1),
                              Pulse_Syntax_Pure.Tm_ForallSL (u2, b2, t2)) ->
                               if
                                 (Pulse_Syntax_Base.eq_univ u1 u2) &&
                                   (Pulse_Syntax_Base.eq_tm
                                      b1.Pulse_Syntax_Base.binder_ty
                                      b2.Pulse_Syntax_Base.binder_ty)
                               then
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Rewrite.fst"
                                            (Prims.of_int (51))
                                            (Prims.of_int (16))
                                            (Prims.of_int (51))
                                            (Prims.of_int (23)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Rewrite.fst"
                                            (Prims.of_int (53))
                                            (Prims.of_int (44))
                                            (Prims.of_int (57))
                                            (Prims.of_int (33)))))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 -> Pulse_Typing_Env.fresh g))
                                   (fun uu___1 ->
                                      (fun x ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Rewrite.fst"
                                                       (Prims.of_int (54))
                                                       (Prims.of_int (17))
                                                       (Prims.of_int (54))
                                                       (Prims.of_int (63)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Rewrite.fst"
                                                       (Prims.of_int (54))
                                                       (Prims.of_int (66))
                                                       (Prims.of_int (57))
                                                       (Prims.of_int (33)))))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Pulse_Typing_Env.push_binding
                                                      g x
                                                      b1.Pulse_Syntax_Base.binder_ppname
                                                      b1.Pulse_Syntax_Base.binder_ty))
                                              (fun uu___1 ->
                                                 (fun g' ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Rewrite.fst"
                                                                  (Prims.of_int (55))
                                                                  (Prims.of_int (17))
                                                                  (Prims.of_int (55))
                                                                  (Prims.of_int (36)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Rewrite.fst"
                                                                  (Prims.of_int (55))
                                                                  (Prims.of_int (39))
                                                                  (Prims.of_int (57))
                                                                  (Prims.of_int (33)))))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___1 ->
                                                               ((b1.Pulse_Syntax_Base.binder_ppname),
                                                                 x)))
                                                         (fun uu___1 ->
                                                            (fun nx ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (82)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (33)))))
                                                                    (
                                                                    Obj.magic
                                                                    (check_vprop_equiv
                                                                    r g'
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    t1 nx)
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    t2 nx)))
                                                                    (
                                                                    fun ext
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))))
                                                              uu___1)))
                                                   uu___1))) uu___1)
                               else check_vprop_equiv_ext r g p q
                           | (Pulse_Syntax_Pure.Tm_Star (p1, p2),
                              Pulse_Syntax_Pure.Tm_Star (q1, q2)) ->
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Rewrite.fst"
                                          (Prims.of_int (61))
                                          (Prims.of_int (17))
                                          (Prims.of_int (61))
                                          (Prims.of_int (44)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Rewrite.fst"
                                          (Prims.of_int (61))
                                          (Prims.of_int (47))
                                          (Prims.of_int (63))
                                          (Prims.of_int (37)))))
                                 (Obj.magic (check_vprop_equiv r g p1 q1))
                                 (fun uu___1 ->
                                    (fun ext1 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Rewrite.fst"
                                                     (Prims.of_int (62))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (62))
                                                     (Prims.of_int (44)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Rewrite.fst"
                                                     (Prims.of_int (63))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (63))
                                                     (Prims.of_int (37)))))
                                            (Obj.magic
                                               (check_vprop_equiv r g p2 q2))
                                            (fun ext2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 -> ())))) uu___1)
                           | uu___1 -> check_vprop_equiv_ext r g p q)))
            uu___3 uu___2 uu___1 uu___
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
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Rewrite.fst"
                         (Prims.of_int (78)) (Prims.of_int (10))
                         (Prims.of_int (78)) (Prims.of_int (48)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Rewrite.fst"
                         (Prims.of_int (78)) (Prims.of_int (51))
                         (Prims.of_int (84)) (Prims.of_int (116)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Checker_Pure.push_context "check_rewrite"
                        t.Pulse_Syntax_Base.range1 g))
                (fun uu___ ->
                   (fun g1 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Rewrite.fst"
                                    (Prims.of_int (79)) (Prims.of_int (32))
                                    (Prims.of_int (79)) (Prims.of_int (38)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Rewrite.fst"
                                    (Prims.of_int (78)) (Prims.of_int (51))
                                    (Prims.of_int (84)) (Prims.of_int (116)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> t.Pulse_Syntax_Base.term1))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | Pulse_Syntax_Base.Tm_Rewrite
                                     { Pulse_Syntax_Base.t11 = p;
                                       Pulse_Syntax_Base.t21 = q;_}
                                     ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Rewrite.fst"
                                                   (Prims.of_int (80))
                                                   (Prims.of_int (26))
                                                   (Prims.of_int (80))
                                                   (Prims.of_int (41)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Rewrite.fst"
                                                   (Prims.of_int (79))
                                                   (Prims.of_int (41))
                                                   (Prims.of_int (84))
                                                   (Prims.of_int (116)))))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.check_vprop
                                                g1 p))
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
                                                                  "Pulse.Checker.Rewrite.fst"
                                                                  (Prims.of_int (81))
                                                                  (Prims.of_int (26))
                                                                  (Prims.of_int (81))
                                                                  (Prims.of_int (41)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Rewrite.fst"
                                                                  (Prims.of_int (80))
                                                                  (Prims.of_int (44))
                                                                  (Prims.of_int (84))
                                                                  (Prims.of_int (116)))))
                                                         (Obj.magic
                                                            (Pulse_Checker_Pure.check_vprop
                                                               g1 q))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               match uu___2
                                                               with
                                                               | Prims.Mkdtuple2
                                                                   (q1,
                                                                    q_typing)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (116)))))
                                                                    (Obj.magic
                                                                    (check_vprop_equiv
                                                                    t.Pulse_Syntax_Base.range1
                                                                    g1 p1 q1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    equiv_p_q
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (84))
                                                                    Prims.int_one
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (116)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Rewrite
                                                                    (g1, p1,
                                                                    q1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (84))
                                                                    Prims.int_one
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (116)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (98)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g1
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Ghost)
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t11
                                                                    = p1;
                                                                    Pulse_Syntax_Base.t21
                                                                    = q1
                                                                    }))
                                                                    (Pulse_Typing.comp_rewrite
                                                                    p1 q1) d
                                                                    post_hint))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    g pre ()
                                                                    uu___3
                                                                    res_ppname))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g pre
                                                                    uu___3
                                                                    post_hint
                                                                    t.Pulse_Syntax_Base.range1))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                              uu___2)))
                                               uu___1))) uu___))) uu___)