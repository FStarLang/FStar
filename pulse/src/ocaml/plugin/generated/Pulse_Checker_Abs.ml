open Prims
let rec (arrow_of_abs :
  Pulse_Syntax_Base.st_term ->
    (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Abs.fst" (Prims.of_int (19))
               (Prims.of_int (44)) (Prims.of_int (19)) (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Abs.fst" (Prims.of_int (19))
               (Prims.of_int (3)) (Prims.of_int (26)) (Prims.of_int (29)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> t.Pulse_Syntax_Base.term1))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | Pulse_Syntax_Base.Tm_Abs
                { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                  Pulse_Syntax_Base.ascription = ascription;
                  Pulse_Syntax_Base.body = body;_}
                ->
                if
                  Pulse_Syntax_Base.uu___is_Tm_Abs
                    body.Pulse_Syntax_Base.term1
                then
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                   (Prims.of_int (22)) (Prims.of_int (16))
                                   (Prims.of_int (22)) (Prims.of_int (33)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                   (Prims.of_int (23)) (Prims.of_int (6))
                                   (Prims.of_int (23)) (Prims.of_int (30)))))
                          (Obj.magic (arrow_of_abs body))
                          (fun arr ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 ->
                                  Pulse_Syntax_Pure.tm_arrow b q
                                    (Pulse_Syntax_Base.C_Tot arr)))))
                else
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             Pulse_Syntax_Pure.tm_arrow b q ascription))))
           uu___)
let rec (rebuild_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      FStar_Tactics_NamedView.term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun annot ->
        match ((t.Pulse_Syntax_Base.term1),
                (FStar_Reflection_V2_Builtins.inspect_ln annot))
        with
        | (Pulse_Syntax_Base.Tm_Abs
           { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
             Pulse_Syntax_Base.ascription = Pulse_Syntax_Base.C_Tot un;
             Pulse_Syntax_Base.body = body;_},
           FStar_Reflection_V2_Data.Tv_Arrow (b', c')) ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                       (Prims.of_int (33)) (Prims.of_int (15))
                       (Prims.of_int (33)) (Prims.of_int (53)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                       (Prims.of_int (33)) (Prims.of_int (56))
                       (Prims.of_int (43)) (Prims.of_int (41)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Pulse_Readback.readback_ty
                      (FStar_Reflection_V2_Builtins.inspect_binder b').FStar_Reflection_V2_Data.sort2))
              (fun uu___ ->
                 (fun ty ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (34)) (Prims.of_int (17))
                                  (Prims.of_int (34)) (Prims.of_int (34)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (35)) (Prims.of_int (6))
                                  (Prims.of_int (43)) (Prims.of_int (41)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               FStar_Reflection_V2_Builtins.inspect_comp c'))
                         (fun uu___ ->
                            (fun comp ->
                               match (ty, comp) with
                               | (FStar_Pervasives_Native.Some ty1,
                                  FStar_Reflection_V2_Data.C_Total res_ty) ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (37))
                                                 (Prims.of_int (18))
                                                 (Prims.of_int (37))
                                                 (Prims.of_int (66)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (37))
                                                 (Prims.of_int (71))
                                                 (Prims.of_int (39))
                                                 (Prims.of_int (67)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___ ->
                                              {
                                                Pulse_Syntax_Base.binder_ty =
                                                  ty1;
                                                Pulse_Syntax_Base.binder_ppname
                                                  =
                                                  (b.Pulse_Syntax_Base.binder_ppname)
                                              }))
                                        (fun uu___ ->
                                           (fun b1 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Abs.fst"
                                                            (Prims.of_int (38))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (38))
                                                            (Prims.of_int (44)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Abs.fst"
                                                            (Prims.of_int (39))
                                                            (Prims.of_int (10))
                                                            (Prims.of_int (39))
                                                            (Prims.of_int (66)))))
                                                   (Obj.magic
                                                      (rebuild_abs g body
                                                         res_ty))
                                                   (fun body1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___ ->
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
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    un);
                                                                    Pulse_Syntax_Base.body
                                                                    = body1
                                                                  });
                                                             Pulse_Syntax_Base.range2
                                                               =
                                                               (t.Pulse_Syntax_Base.range2)
                                                           })))) uu___))
                               | uu___ ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (42))
                                                 (Prims.of_int (12))
                                                 (Prims.of_int (43))
                                                 (Prims.of_int (41)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (41))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (43))
                                                 (Prims.of_int (41)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Abs.fst"
                                                       (Prims.of_int (43))
                                                       (Prims.of_int (16))
                                                       (Prims.of_int (43))
                                                       (Prims.of_int (40)))))
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
                                                    annot))
                                              (fun uu___1 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      Prims.strcat
                                                        "Unexpected type of abstraction: "
                                                        (Prims.strcat uu___1
                                                           "")))))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              Obj.magic
                                                (Pulse_Typing_Env.fail g
                                                   (FStar_Pervasives_Native.Some
                                                      (t.Pulse_Syntax_Base.range2))
                                                   uu___1)) uu___1))) uu___)))
                   uu___)
        | (Pulse_Syntax_Base.Tm_Abs
           { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
             Pulse_Syntax_Base.ascription = uu___;
             Pulse_Syntax_Base.body = body;_},
           FStar_Reflection_V2_Data.Tv_Arrow (b', c')) ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                       (Prims.of_int (46)) (Prims.of_int (15))
                       (Prims.of_int (46)) (Prims.of_int (53)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                       (Prims.of_int (46)) (Prims.of_int (56))
                       (Prims.of_int (63)) (Prims.of_int (51)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    Pulse_Readback.readback_ty
                      (FStar_Reflection_V2_Builtins.inspect_binder b').FStar_Reflection_V2_Data.sort2))
              (fun uu___1 ->
                 (fun ty ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (47)) (Prims.of_int (17))
                                  (Prims.of_int (47)) (Prims.of_int (34)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (48)) (Prims.of_int (6))
                                  (Prims.of_int (63)) (Prims.of_int (51)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Reflection_V2_Builtins.inspect_comp c'))
                         (fun uu___1 ->
                            (fun comp ->
                               match (ty, comp) with
                               | (FStar_Pervasives_Native.Some ty1,
                                  FStar_Reflection_V2_Data.C_Total res) ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (50))
                                                 (Prims.of_int (16))
                                                 (Prims.of_int (50))
                                                 (Prims.of_int (33)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (51))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (58))
                                                 (Prims.of_int (62)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              Pulse_Readback.readback_comp
                                                res))
                                        (fun uu___1 ->
                                           (fun c ->
                                              match c with
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Abs.fst"
                                                                   (Prims.of_int (54))
                                                                   (Prims.of_int (22))
                                                                   (Prims.of_int (55))
                                                                   (Prims.of_int (49)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Abs.fst"
                                                                   (Prims.of_int (53))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (55))
                                                                   (Prims.of_int (49)))))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (48)))))
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
                                                                    res))
                                                                (fun uu___1
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.strcat
                                                                    "Unexpected computation type in abstraction: "
                                                                    (Prims.strcat
                                                                    uu___1 "")))))
                                                          (fun uu___1 ->
                                                             (fun uu___1 ->
                                                                Obj.magic
                                                                  (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    uu___1))
                                                               uu___1)))
                                              | FStar_Pervasives_Native.Some
                                                  c1 ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___1 ->
                                                             {
                                                               Pulse_Syntax_Base.term1
                                                                 =
                                                                 (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = ty1;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    =
                                                                    (b.Pulse_Syntax_Base.binder_ppname)
                                                                    };
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    = c1;
                                                                    Pulse_Syntax_Base.body
                                                                    = body
                                                                    });
                                                               Pulse_Syntax_Base.range2
                                                                 =
                                                                 (t.Pulse_Syntax_Base.range2)
                                                             })))) uu___1))
                               | uu___1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (62))
                                                 (Prims.of_int (20))
                                                 (Prims.of_int (63))
                                                 (Prims.of_int (51)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (61))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (63))
                                                 (Prims.of_int (51)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Abs.fst"
                                                       (Prims.of_int (63))
                                                       (Prims.of_int (26))
                                                       (Prims.of_int (63))
                                                       (Prims.of_int (50)))))
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
                                                    annot))
                                              (fun uu___2 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 ->
                                                      Prims.strcat
                                                        "Unexpected type of abstraction: "
                                                        (Prims.strcat uu___2
                                                           "")))))
                                        (fun uu___2 ->
                                           (fun uu___2 ->
                                              Obj.magic
                                                (Pulse_Typing_Env.fail g
                                                   (FStar_Pervasives_Native.Some
                                                      (t.Pulse_Syntax_Base.range2))
                                                   uu___2)) uu___2))) uu___1)))
                   uu___1)
        | uu___ ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                       (Prims.of_int (67)) (Prims.of_int (16))
                       (Prims.of_int (68)) (Prims.of_int (47)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                       (Prims.of_int (66)) (Prims.of_int (6))
                       (Prims.of_int (68)) (Prims.of_int (47)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                             (Prims.of_int (68)) (Prims.of_int (22))
                             (Prims.of_int (68)) (Prims.of_int (46)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "prims.fst"
                             (Prims.of_int (590)) (Prims.of_int (19))
                             (Prims.of_int (590)) (Prims.of_int (31)))))
                    (Obj.magic
                       (FStar_Tactics_V2_Builtins.term_to_string annot))
                    (fun uu___1 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___2 ->
                            Prims.strcat
                              "Unexpected arity of abstraction: expected a term of type "
                              (Prims.strcat uu___1 "")))))
              (fun uu___1 ->
                 (fun uu___1 ->
                    Obj.magic
                      (Pulse_Typing_Env.fail g
                         (FStar_Pervasives_Native.Some
                            (t.Pulse_Syntax_Base.range2)) uu___1)) uu___1)
let (preprocess_abs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                 (Prims.of_int (74)) (Prims.of_int (16)) (Prims.of_int (74))
                 (Prims.of_int (30)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                 (Prims.of_int (74)) (Prims.of_int (33)) (Prims.of_int (82))
                 (Prims.of_int (51))))) (Obj.magic (arrow_of_abs t))
        (fun uu___ ->
           (fun annot ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                            (Prims.of_int (75)) (Prims.of_int (19))
                            (Prims.of_int (75)) (Prims.of_int (72)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                            (Prims.of_int (74)) (Prims.of_int (33))
                            (Prims.of_int (82)) (Prims.of_int (51)))))
                   (Obj.magic
                      (Pulse_Checker_Pure.instantiate_term_implicits g annot))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | (annot1, uu___1) ->
                             (match annot1.Pulse_Syntax_Base.t with
                              | Pulse_Syntax_Base.Tm_FStar annot2 ->
                                  Obj.magic (rebuild_abs g t annot2)
                              | uu___2 ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Abs.fst"
                                                (Prims.of_int (81))
                                                (Prims.of_int (17))
                                                (Prims.of_int (82))
                                                (Prims.of_int (51)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Abs.fst"
                                                (Prims.of_int (80))
                                                (Prims.of_int (6))
                                                (Prims.of_int (82))
                                                (Prims.of_int (51)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Abs.fst"
                                                      (Prims.of_int (82))
                                                      (Prims.of_int (26))
                                                      (Prims.of_int (82))
                                                      (Prims.of_int (50)))))
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
                                                   annot1))
                                             (fun uu___3 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___4 ->
                                                     Prims.strcat
                                                       "Expected an arrow type as an annotation, got "
                                                       (Prims.strcat uu___3
                                                          "")))))
                                       (fun uu___3 ->
                                          (fun uu___3 ->
                                             Obj.magic
                                               (Pulse_Typing_Env.fail g
                                                  (FStar_Pervasives_Native.Some
                                                     (t.Pulse_Syntax_Base.range2))
                                                  uu___3)) uu___3)))) uu___)))
             uu___)
let (check_effect_annotation :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.range ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.comp -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun r ->
               fun c_annot ->
                 fun c_computed ->
                   match (c_annot, c_computed) with
                   | (Pulse_Syntax_Base.C_Tot uu___, Pulse_Syntax_Base.C_Tot
                      uu___1) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 -> ())))
                   | (Pulse_Syntax_Base.C_ST uu___, Pulse_Syntax_Base.C_ST
                      uu___1) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 -> ())))
                   | (Pulse_Syntax_Base.C_STAtomic (i, uu___),
                      Pulse_Syntax_Base.C_STAtomic (j, uu___1)) ->
                       Obj.magic
                         (Obj.repr
                            (if Pulse_Syntax_Base.eq_tm i j
                             then
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 -> ()))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (93))
                                             (Prims.of_int (16))
                                             (Prims.of_int (95))
                                             (Prims.of_int (39)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (92))
                                             (Prims.of_int (9))
                                             (Prims.of_int (95))
                                             (Prims.of_int (39)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (95))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (95))
                                                   (Prims.of_int (38)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (93))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (95))
                                                   (Prims.of_int (39)))))
                                          (Obj.magic
                                             (Pulse_Syntax_Printer.term_to_string
                                                j))
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (93))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (95))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (93))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (95))
                                                              (Prims.of_int (39)))))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (38)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                           (Obj.magic
                                                              (Pulse_Syntax_Printer.term_to_string
                                                                 i))
                                                           (fun uu___4 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___5
                                                                   ->
                                                                   fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Annotated effect expects only invariants in "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " to be opened; but computed effect claims that invariants "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " are opened")))))
                                                     (fun uu___4 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___5 ->
                                                             uu___4 uu___3))))
                                               uu___3)))
                                    (fun uu___3 ->
                                       (fun uu___3 ->
                                          Obj.magic
                                            (Pulse_Typing_Env.fail g
                                               (FStar_Pervasives_Native.Some
                                                  (i.Pulse_Syntax_Base.range1))
                                               uu___3)) uu___3))))
                   | (Pulse_Syntax_Base.C_STGhost (i, uu___),
                      Pulse_Syntax_Base.C_STGhost (j, uu___1)) ->
                       Obj.magic
                         (Obj.repr
                            (if Pulse_Syntax_Base.eq_tm i j
                             then
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 -> ()))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (93))
                                             (Prims.of_int (16))
                                             (Prims.of_int (95))
                                             (Prims.of_int (39)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Abs.fst"
                                             (Prims.of_int (92))
                                             (Prims.of_int (9))
                                             (Prims.of_int (95))
                                             (Prims.of_int (39)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (95))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (95))
                                                   (Prims.of_int (38)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Abs.fst"
                                                   (Prims.of_int (93))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (95))
                                                   (Prims.of_int (39)))))
                                          (Obj.magic
                                             (Pulse_Syntax_Printer.term_to_string
                                                j))
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (93))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (95))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Abs.fst"
                                                              (Prims.of_int (93))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (95))
                                                              (Prims.of_int (39)))))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (38)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                           (Obj.magic
                                                              (Pulse_Syntax_Printer.term_to_string
                                                                 i))
                                                           (fun uu___4 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___5
                                                                   ->
                                                                   fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Annotated effect expects only invariants in "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " to be opened; but computed effect claims that invariants "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " are opened")))))
                                                     (fun uu___4 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___5 ->
                                                             uu___4 uu___3))))
                                               uu___3)))
                                    (fun uu___3 ->
                                       (fun uu___3 ->
                                          Obj.magic
                                            (Pulse_Typing_Env.fail g
                                               (FStar_Pervasives_Native.Some
                                                  (i.Pulse_Syntax_Base.range1))
                                               uu___3)) uu___3))))
                   | (uu___, uu___1) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Abs.fst"
                                        (Prims.of_int (98))
                                        (Prims.of_int (11))
                                        (Prims.of_int (100))
                                        (Prims.of_int (45)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Abs.fst"
                                        (Prims.of_int (97))
                                        (Prims.of_int (4))
                                        (Prims.of_int (100))
                                        (Prims.of_int (45)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Abs.fst"
                                              (Prims.of_int (100))
                                              (Prims.of_int (18))
                                              (Prims.of_int (100))
                                              (Prims.of_int (44)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Abs.fst"
                                              (Prims.of_int (98))
                                              (Prims.of_int (11))
                                              (Prims.of_int (100))
                                              (Prims.of_int (45)))))
                                     (Obj.magic
                                        (Pulse_Syntax_Printer.tag_of_comp
                                           c_computed))
                                     (fun uu___2 ->
                                        (fun uu___2 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Abs.fst"
                                                         (Prims.of_int (98))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (100))
                                                         (Prims.of_int (45)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Abs.fst"
                                                         (Prims.of_int (98))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (100))
                                                         (Prims.of_int (45)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Abs.fst"
                                                               (Prims.of_int (99))
                                                               (Prims.of_int (18))
                                                               (Prims.of_int (99))
                                                               (Prims.of_int (41)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Printf.fst"
                                                               (Prims.of_int (121))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (123))
                                                               (Prims.of_int (44)))))
                                                      (Obj.magic
                                                         (Pulse_Syntax_Printer.tag_of_comp
                                                            c_annot))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              fun x ->
                                                                Prims.strcat
                                                                  (Prims.strcat
                                                                    "Expected effect "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " but this function body has effect "))
                                                                  (Prims.strcat
                                                                    x "")))))
                                                (fun uu___3 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        uu___3 uu___2))))
                                          uu___2)))
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     Obj.magic
                                       (Pulse_Typing_Env.fail g
                                          (FStar_Pervasives_Native.Some r)
                                          uu___2)) uu___2)))) uu___3 uu___2
            uu___1 uu___
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
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (109)) (Prims.of_int (14))
                   (Prims.of_int (109)) (Prims.of_int (21)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (110)) (Prims.of_int (2))
                   (Prims.of_int (170)) (Prims.of_int (29)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> t.Pulse_Syntax_Base.range2))
          (fun uu___ ->
             (fun range ->
                match t.Pulse_Syntax_Base.term1 with
                | Pulse_Syntax_Base.Tm_Abs
                    {
                      Pulse_Syntax_Base.b =
                        { Pulse_Syntax_Base.binder_ty = t1;
                          Pulse_Syntax_Base.binder_ppname = ppname;_};
                      Pulse_Syntax_Base.q = qual;
                      Pulse_Syntax_Base.ascription = c;
                      Pulse_Syntax_Base.body = body;_}
                    ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (114)) (Prims.of_int (24))
                                  (Prims.of_int (114)) (Prims.of_int (42)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                                  (Prims.of_int (111)) (Prims.of_int (84))
                                  (Prims.of_int (170)) (Prims.of_int (29)))))
                         (Obj.magic (Pulse_Checker_Pure.check_tot_term g t1))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | FStar_Pervasives.Mkdtuple3
                                   (t2, uu___1, uu___2) ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (115))
                                                 (Prims.of_int (28))
                                                 (Prims.of_int (115))
                                                 (Prims.of_int (46)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Abs.fst"
                                                 (Prims.of_int (114))
                                                 (Prims.of_int (45))
                                                 (Prims.of_int (170))
                                                 (Prims.of_int (29)))))
                                        (Obj.magic
                                           (Pulse_Checker_Pure.check_universe
                                              g t2))
                                        (fun uu___3 ->
                                           (fun uu___3 ->
                                              match uu___3 with
                                              | Prims.Mkdtuple2 (u, t_typing)
                                                  ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Abs.fst"
                                                                (Prims.of_int (116))
                                                                (Prims.of_int (12))
                                                                (Prims.of_int (116))
                                                                (Prims.of_int (19)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Abs.fst"
                                                                (Prims.of_int (116))
                                                                (Prims.of_int (22))
                                                                (Prims.of_int (170))
                                                                (Prims.of_int (29)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             Pulse_Typing_Env.fresh
                                                               g))
                                                       (fun uu___4 ->
                                                          (fun x ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (22)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (ppname,
                                                                    x)))
                                                                  (fun uu___4
                                                                    ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Pure.tm_var
                                                                    {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    = ppname
                                                                    }))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun var
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    ppname t2))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body px))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body_opened
                                                                    ->
                                                                    match 
                                                                    body_opened.Pulse_Syntax_Base.term1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Abs
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (check_abs_core
                                                                    g'
                                                                    body_opened
                                                                    check))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
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
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (check_effect_annotation
                                                                    g'
                                                                    body1.Pulse_Syntax_Base.range2
                                                                    c c_body))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname
                                                                    };
                                                                    Pulse_Syntax_Base.q
                                                                    = qual;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c_body x);
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
                                                                    = ppname
                                                                    } qual
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c_body x))),
                                                                    (Pulse_Typing.T_Abs
                                                                    (g, x,
                                                                    qual,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname
                                                                    }, u,
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body1 x),
                                                                    c_body,
                                                                    (),
                                                                    body_typing)))))))
                                                                    uu___5))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (match c
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_Tot
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range2))
                                                                    "Unexpected error: found a total computation annotation on a top-level function"))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    ((Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c) px),
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c) px)),
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.open_term'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c) var
                                                                    Prims.int_one)))))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (pre_opened,
                                                                    ret_ty,
                                                                    post_hint_body)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop
                                                                    g'
                                                                    pre_opened))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (pre_opened1,
                                                                    pre_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Naming.close_term
                                                                    pre_opened1
                                                                    x))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun pre
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (match post_hint_body
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range2))
                                                                    "Top-level functions must be annotated with pre and post conditions")
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    post ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (130)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.intro_post_hint
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "post_hint_typing"
                                                                    range g')
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c))
                                                                    ret_ty
                                                                    post))
                                                                    (fun
                                                                    post_hint_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    post_hint_typing))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_fret"))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    ppname1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    pre_opened1
                                                                    () post
                                                                    ppname1
                                                                    body_opened))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g'
                                                                    pre_opened1
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    post) r
                                                                    ppname1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
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
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Abs.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (check_effect_annotation
                                                                    g'
                                                                    body1.Pulse_Syntax_Base.range2
                                                                    c c_body))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname1
                                                                    };
                                                                    Pulse_Syntax_Base.q
                                                                    = qual;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c_body x);
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
                                                                    = ppname1
                                                                    } qual
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c_body x))),
                                                                    (Pulse_Typing.T_Abs
                                                                    (g, x,
                                                                    qual,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = ppname1
                                                                    }, u,
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body1 x),
                                                                    c_body,
                                                                    (),
                                                                    body_typing)))))))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                            uu___4))) uu___3)))
                              uu___))) uu___)
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
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (174)) (Prims.of_int (10))
                   (Prims.of_int (174)) (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Abs.fst"
                   (Prims.of_int (175)) (Prims.of_int (2))
                   (Prims.of_int (175)) (Prims.of_int (26)))))
          (Obj.magic (preprocess_abs g t))
          (fun uu___ ->
             (fun t1 -> Obj.magic (check_abs_core g t1 check)) uu___)