open Prims
let (rt_recheck :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Tactics_NamedView.term ->
        FStar_Reflection_Types.typ ->
          unit ->
            ((unit, unit, unit) FStar_Reflection_Typing.tot_typing, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun gg ->
    fun g ->
      fun e ->
        fun ty ->
          fun uu___ ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (34)) (Prims.of_int (2))
                       (Prims.of_int (39)) (Prims.of_int (4)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (40)) (Prims.of_int (2))
                       (Prims.of_int (42)) (Prims.of_int (58)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                             (Prims.of_int (34)) (Prims.of_int (41))
                             (Prims.of_int (39)) (Prims.of_int (4)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                             (Prims.of_int (34)) (Prims.of_int (2))
                             (Prims.of_int (39)) (Prims.of_int (4)))))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.WithInv.fst"
                                   (Prims.of_int (35)) (Prims.of_int (4))
                                   (Prims.of_int (38)) (Prims.of_int (11)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.WithInv.fst"
                                   (Prims.of_int (34)) (Prims.of_int (41))
                                   (Prims.of_int (39)) (Prims.of_int (4)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.WithInv.fst"
                                         (Prims.of_int (36))
                                         (Prims.of_int (6))
                                         (Prims.of_int (38))
                                         (Prims.of_int (11)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.WithInv.fst"
                                         (Prims.of_int (35))
                                         (Prims.of_int (4))
                                         (Prims.of_int (38))
                                         (Prims.of_int (11)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.WithInv.fst"
                                               (Prims.of_int (36))
                                               (Prims.of_int (6))
                                               (Prims.of_int (36))
                                               (Prims.of_int (10)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.WithInv.fst"
                                               (Prims.of_int (36))
                                               (Prims.of_int (6))
                                               (Prims.of_int (38))
                                               (Prims.of_int (11)))))
                                      (Obj.magic
                                         (Pulse_PP.pp
                                            Pulse_PP.printable_fstar_term e))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (37))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (38))
                                                          (Prims.of_int (11)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (36))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (38))
                                                          (Prims.of_int (11)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithInv.fst"
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (11)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithInv.fst"
                                                                (Prims.of_int (37))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (11)))))
                                                       (Obj.magic
                                                          (Pulse_PP.pp
                                                             Pulse_PP.printable_fstar_term
                                                             ty))
                                                       (fun uu___2 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___3 ->
                                                               FStar_Pprint.op_Hat_Slash_Hat
                                                                 (FStar_Pprint.doc_of_string
                                                                    "at type")
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
                                        FStar_Pprint.op_Hat_Slash_Hat
                                          (FStar_Pprint.doc_of_string
                                             "Re-checking") uu___1))))
                          (fun uu___1 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 -> [uu___1]))))
                    (fun uu___1 ->
                       (fun uu___1 ->
                          Obj.magic
                            (Pulse_Typing_Env.info_doc gg
                               (FStar_Pervasives_Native.Some
                                  (FStar_Reflection_V2_Builtins.range_of_term
                                     e)) uu___1)) uu___1)))
              (fun uu___1 ->
                 (fun uu___1 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.WithInv.fst"
                                  (Prims.of_int (40)) (Prims.of_int (8))
                                  (Prims.of_int (40)) (Prims.of_int (42)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.WithInv.fst"
                                  (Prims.of_int (40)) (Prims.of_int (2))
                                  (Prims.of_int (42)) (Prims.of_int (58)))))
                         (Obj.magic
                            (FStar_Tactics_V2_Builtins.core_check_term g e ty
                               FStar_TypeChecker_Core.E_Total))
                         (fun uu___2 ->
                            match uu___2 with
                            | (FStar_Pervasives_Native.Some tok, uu___3) ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 ->
                                     FStar_Reflection_Typing.T_Token
                                       (g, e,
                                         (FStar_TypeChecker_Core.E_Total, ty),
                                         ()))
                            | (FStar_Pervasives_Native.None, uu___3) ->
                                FStar_Tactics_V2_Derived.fail
                                  "Checker.WithInv: rt_recheck failed")))
                   uu___1)
let (recheck :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.typ ->
        unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun ty -> fun uu___ -> Pulse_Checker_Pure.core_check_tot_term g e ty
let (term_remove_inv :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun inv ->
         fun tm ->
           match tm.Pulse_Syntax_Base.t with
           | Pulse_Syntax_Base.Tm_Star (tm1, inv') ->
               if Pulse_Syntax_Base.eq_tm inv inv'
               then
                 Obj.magic
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> tm1))
               else
                 Obj.magic (FStar_Tactics_V2_Derived.fail "term_remove_inv")
           | uu___ ->
               Obj.magic
                 (FStar_Tactics_V2_Derived.fail
                    "term_remove_inv: not a star?")) uu___1 uu___
let (st_comp_remove_inv :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.st_comp ->
      (Pulse_Syntax_Base.st_comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun inv ->
    fun c ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                 (Prims.of_int (57)) (Prims.of_int (17)) (Prims.of_int (57))
                 (Prims.of_int (42)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                 (Prims.of_int (57)) (Prims.of_int (4)) (Prims.of_int (58))
                 (Prims.of_int (44)))))
        (Obj.magic (term_remove_inv inv c.Pulse_Syntax_Base.pre))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                            (Prims.of_int (58)) (Prims.of_int (18))
                            (Prims.of_int (58)) (Prims.of_int (44)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                            (Prims.of_int (57)) (Prims.of_int (4))
                            (Prims.of_int (58)) (Prims.of_int (44)))))
                   (Obj.magic (term_remove_inv inv c.Pulse_Syntax_Base.post))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           {
                             Pulse_Syntax_Base.u = (c.Pulse_Syntax_Base.u);
                             Pulse_Syntax_Base.res =
                               (c.Pulse_Syntax_Base.res);
                             Pulse_Syntax_Base.pre = uu___;
                             Pulse_Syntax_Base.post = uu___1
                           })))) uu___)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
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
            fun t ->
              fun check1 ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (71)) (Prims.of_int (52))
                           (Prims.of_int (71)) (Prims.of_int (58)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (70)) (Prims.of_int (46))
                           (Prims.of_int (212)) (Prims.of_int (61)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> t.Pulse_Syntax_Base.term1))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | Pulse_Syntax_Base.Tm_WithInv
                            { Pulse_Syntax_Base.name1 = inv_tm;
                              Pulse_Syntax_Base.body6 = body;
                              Pulse_Syntax_Base.returns_inv = returns_inv;_}
                            ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (75))
                                          (Prims.of_int (19))
                                          (Prims.of_int (75))
                                          (Prims.of_int (29)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (75))
                                          (Prims.of_int (32))
                                          (Prims.of_int (212))
                                          (Prims.of_int (61)))))
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 ->
                                       body.Pulse_Syntax_Base.range2))
                                 (fun uu___1 ->
                                    (fun body_range ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.WithInv.fst"
                                                     (Prims.of_int (78))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (85))
                                                     (Prims.of_int (67)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.WithInv.fst"
                                                     (Prims.of_int (86))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (212))
                                                     (Prims.of_int (61)))))
                                            (match (returns_inv, post_hint)
                                             with
                                             | (FStar_Pervasives_Native.None,
                                                FStar_Pervasives_Native.Some
                                                p) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___1 -> p)))
                                             | (FStar_Pervasives_Native.Some
                                                p,
                                                FStar_Pervasives_Native.None)
                                                 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (Pulse_Checker_Base.intro_post_hint
                                                         g
                                                         FStar_Pervasives_Native.None
                                                         FStar_Pervasives_Native.None
                                                         p))
                                             | (FStar_Pervasives_Native.Some
                                                p,
                                                FStar_Pervasives_Native.Some
                                                q) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (Pulse_Typing_Env.fail
                                                         g
                                                         (FStar_Pervasives_Native.Some
                                                            (t.Pulse_Syntax_Base.range2))
                                                         "Fatal: multiple posts hint on with_invariant"))
                                             | (uu___1, uu___2) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (Pulse_Typing_Env.fail
                                                         g
                                                         (FStar_Pervasives_Native.Some
                                                            (t.Pulse_Syntax_Base.range2))
                                                         "Fatal: no post hint on with_invariant")))
                                            (fun uu___1 ->
                                               (fun post ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithInv.fst"
                                                                (Prims.of_int (87))
                                                                (Prims.of_int (18))
                                                                (Prims.of_int (87))
                                                                (Prims.of_int (27)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithInv.fst"
                                                                (Prims.of_int (89))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (212))
                                                                (Prims.of_int (61)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___1 ->
                                                             FStar_Pervasives_Native.Some
                                                               post))
                                                       (fun uu___1 ->
                                                          (fun post_hint1 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (3)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (82)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_option
                                                                    Pulse_PP.uu___53)
                                                                    post_hint1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "Checker.WithInv: using post_hint =")
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    [uu___1]))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.info_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    uu___1))
                                                                    uu___1)))
                                                                  (fun uu___1
                                                                    ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.compute_term_type
                                                                    g inv_tm))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (inv_tm1,
                                                                    eff,
                                                                    inv_tm_ty,
                                                                    inv_tm_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (if
                                                                    eff <>
                                                                    FStar_TypeChecker_Core.E_Total
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (inv_tm1.Pulse_Syntax_Base.range1))
                                                                    "Ghost effect on inv?"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (match 
                                                                    inv_tm_ty.Pulse_Syntax_Base.t
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Inv
                                                                    p ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    p)))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_FStar
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Pure.is_fvar_app
                                                                    inv_tm1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun ropt
                                                                    ->
                                                                    match ropt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (lid,
                                                                    uu___5,
                                                                    uu___6,
                                                                    FStar_Pervasives_Native.Some
                                                                    tm) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    lid =
                                                                    ["Pulse";
                                                                    "Lib";
                                                                    "Core";
                                                                    "inv"]
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    tm))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    inv_tm_ty))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Does not have invariant type ("
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    ")")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (inv_tm1.Pulse_Syntax_Base.range1))
                                                                    uu___8))
                                                                    uu___8))))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    inv_tm_ty))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "Does not have invariant type ("
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    ")")))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (inv_tm1.Pulse_Syntax_Base.range1))
                                                                    uu___6))
                                                                    uu___6))))
                                                                    uu___5)))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    inv_tm_ty))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Does not have invariant type ("
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    ")")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (inv_tm1.Pulse_Syntax_Base.range1))
                                                                    uu___5))
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    inv_p ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (recheck
                                                                    g inv_p
                                                                    Pulse_Syntax_Base.tm_vprop
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    inv_p_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.tm_star
                                                                    pre inv_p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun pre'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (recheck
                                                                    g pre'
                                                                    Pulse_Syntax_Base.tm_vprop
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pre'_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.tm_star
                                                                    post.Pulse_Typing.post
                                                                    inv_p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post_p'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Elaborate_Pure.elab_term
                                                                    post.Pulse_Typing.ret_ty))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    elab_ret_ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    post.Pulse_Typing.ret_ty))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.elab_env
                                                                    g'))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun r_g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (rt_recheck
                                                                    g' r_g'
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    post_p'
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    x)))
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    Pulse_Syntax_Base.tm_vprop)
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post_p'_typing_src
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post_p'_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    if
                                                                    (FStar_Pervasives_Native.uu___is_None
                                                                    post.Pulse_Typing.ctag_hint)
                                                                    ||
                                                                    (post.Pulse_Typing.ctag_hint
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT))
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Ghost
                                                                    else
                                                                    post.Pulse_Typing.ctag_hint))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    ctag_hint'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (recheck
                                                                    g
                                                                    post.Pulse_Typing.ret_ty
                                                                    (Pulse_Syntax_Pure.tm_type
                                                                    post.Pulse_Typing.u)
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    Pulse_Typing.g
                                                                    = g;
                                                                    Pulse_Typing.ctag_hint
                                                                    =
                                                                    ctag_hint';
                                                                    Pulse_Typing.ret_ty
                                                                    =
                                                                    (post.Pulse_Typing.ret_ty);
                                                                    Pulse_Typing.u
                                                                    =
                                                                    (post.Pulse_Typing.u);
                                                                    Pulse_Typing.ty_typing
                                                                    = ();
                                                                    Pulse_Typing.post
                                                                    = post_p';
                                                                    Pulse_Typing.x
                                                                    = x;
                                                                    Pulse_Typing.post_typing_src
                                                                    = ();
                                                                    Pulse_Typing.post_typing
                                                                    = ()
                                                                    }))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "with_inv_body"))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    ppname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (check1 g
                                                                    pre' ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post')
                                                                    ppname
                                                                    body))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g pre'
                                                                    post' r
                                                                    ppname))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (4)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (4)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (4)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (4)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c_body))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pprint.arbitrary_string
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Checked body at comp type:")
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    [uu___5]))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.info_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    body_range)
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun
                                                                    uu___7 ->
                                                                    fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun
                                                                    inames ->
                                                                    fun i ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Base.with_range
                                                                    (Pulse_Syntax_Base.Tm_FStar
                                                                    (Pulse_Reflection_Util.add_inv_tm
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    inv_p)
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    inames)
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    i)))
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    inames)))))
                                                                    uu___8
                                                                    uu___7
                                                                    uu___6))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    add_iname
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (match c_body
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_ST
                                                                    st ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    body_range)
                                                                    [
                                                                    Pulse_PP.text
                                                                    "This computation is not atomic nor ghost. `with_invariants` blocks can only contain ghost or atomic computations."])
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (inames,
                                                                    st) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (96)))))
                                                                    (Obj.magic
                                                                    (add_iname
                                                                    inames
                                                                    inv_tm1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (96)))))
                                                                    (Obj.magic
                                                                    (st_comp_remove_inv
                                                                    inv_p st))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___6,
                                                                    uu___7)))))
                                                                    uu___6))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (inames,
                                                                    st) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (94)))))
                                                                    (Obj.magic
                                                                    (add_iname
                                                                    inames
                                                                    inv_tm1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (94)))))
                                                                    (Obj.magic
                                                                    (st_comp_remove_inv
                                                                    inv_p st))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (uu___6,
                                                                    uu___7)))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    c_out ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = inv_tm1;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (t.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Atomic))
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun tm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_WithInv
                                                                    (g,
                                                                    inv_tm1,
                                                                    inv_p,
                                                                    (), (),
                                                                    body1,
                                                                    c_out,
                                                                    body_typing)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c_out))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "Returning comp type "
                                                                    (Prims.strcat
                                                                    uu___6 "")))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.info
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    body_range)
                                                                    uu___6))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (tm,
                                                                    c_out, d))
                                                                    res_ppname))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                            uu___1))) uu___1)))
                                      uu___1))) uu___)