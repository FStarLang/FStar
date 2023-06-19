open Prims
let (main' :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.term ->
      FStar_Reflection_Typing.fstar_top_env ->
        ((FStar_Reflection_Types.term * FStar_Reflection_Types.typ), 
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun t ->
           fun pre ->
             fun g ->
               match Pulse_Soundness_Common.check_top_level_environment g
               with
               | FStar_Pervasives_Native.None ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_V2_Derived.fail
                           "pulse main: top-level environment does not include stt at the expected types"))
               | FStar_Pervasives_Native.Some g1 ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (22)) (Prims.of_int (6))
                                    (Prims.of_int (25)) (Prims.of_int (7)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (25)) (Prims.of_int (8))
                                    (Prims.of_int (34)) (Prims.of_int (81)))))
                           (if
                              Pulse_RuntimeUtils.debug_at_level
                                (Pulse_Typing_Env.fstar_env g1) "Pulse"
                            then
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (24))
                                               (Prims.of_int (16))
                                               (Prims.of_int (24))
                                               (Prims.of_int (91)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (23))
                                               (Prims.of_int (11))
                                               (Prims.of_int (25))
                                               (Prims.of_int (7)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Main.fst"
                                                     (Prims.of_int (24))
                                                     (Prims.of_int (67))
                                                     (Prims.of_int (24))
                                                     (Prims.of_int (90)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "prims.fst"
                                                     (Prims.of_int (590))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (590))
                                                     (Prims.of_int (31)))))
                                            (Obj.magic
                                               (Pulse_Syntax_Printer.st_term_to_string
                                                  t))
                                            (fun uu___ ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Prims.strcat
                                                      "About to check pulse term:\n"
                                                      (Prims.strcat uu___
                                                         "\n")))))
                                      (fun uu___ ->
                                         (fun uu___ ->
                                            Obj.magic
                                              (FStar_Tactics_V2_Builtins.print
                                                 uu___)) uu___)))
                            else
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 -> ()))))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (26))
                                               (Prims.of_int (38))
                                               (Prims.of_int (26))
                                               (Prims.of_int (73)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (25))
                                               (Prims.of_int (8))
                                               (Prims.of_int (34))
                                               (Prims.of_int (81)))))
                                      (Obj.magic
                                         (Pulse_Checker_Pure.check_term g1
                                            pre))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            match uu___1 with
                                            | FStar_Pervasives.Mkdtuple3
                                                (pre1, ty, pre_typing) ->
                                                if
                                                  Pulse_Syntax_Base.eq_tm ty
                                                    Pulse_Syntax_Base.Tm_VProp
                                                then
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Main.fst"
                                                                (Prims.of_int (28))
                                                                (Prims.of_int (56))
                                                                (Prims.of_int (28))
                                                                (Prims.of_int (68)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Main.fst"
                                                                (Prims.of_int (28))
                                                                (Prims.of_int (71))
                                                                (Prims.of_int (33))
                                                                (Prims.of_int (27)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 -> ()))
                                                       (fun uu___2 ->
                                                          (fun pre_typing1 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (67)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (27)))))
                                                                  (Obj.magic
                                                                    (Pulse_Checker.check
                                                                    g1 t pre1
                                                                    ()
                                                                    FStar_Pervasives_Native.None))
                                                                  (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t1, c,
                                                                    t_typing)
                                                                    ->
                                                                    ((Pulse_Elaborate_Core.elab_st_typing
                                                                    g1 t1 c
                                                                    t_typing),
                                                                    (Pulse_Elaborate_Pure.elab_comp
                                                                    c))))))
                                                            uu___2))
                                                else
                                                  Obj.magic
                                                    (Pulse_Typing_Env.fail g1
                                                       (FStar_Pervasives_Native.Some
                                                          (t.Pulse_Syntax_Base.range1))
                                                       "pulse main: cannot typecheck pre at type vprop"))
                                           uu___1))) uu___)))) uu___2 uu___1
          uu___
let (main :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.term -> FStar_Reflection_Typing.dsl_tac_t)
  = fun t -> fun pre -> main' t pre
let (check_pulse :
  Prims.string Prims.list ->
    (Prims.string * Prims.string) Prims.list ->
      Prims.string ->
        Prims.string ->
          Prims.int -> Prims.int -> FStar_Reflection_Typing.dsl_tac_t)
  =
  fun namespaces ->
    fun module_abbrevs ->
      fun content ->
        fun file_name ->
          fun line ->
            fun col ->
              fun env ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (46)) (Prims.of_int (12))
                           (Prims.of_int (46)) (Prims.of_int (97)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (46)) (Prims.of_int (6))
                           (Prims.of_int (52)) (Prims.of_int (22)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_ASTBuilder.parse_pulse env namespaces
                          module_abbrevs content file_name line col))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | FStar_Pervasives.Inl st_term ->
                            Obj.magic
                              (main st_term Pulse_Syntax_Base.Tm_Emp env)
                        | FStar_Pervasives.Inr (msg, range) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (50))
                                          (Prims.of_int (15))
                                          (Prims.of_int (52))
                                          (Prims.of_int (22)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (50))
                                          (Prims.of_int (8))
                                          (Prims.of_int (52))
                                          (Prims.of_int (22)))))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (50))
                                                (Prims.of_int (15))
                                                (Prims.of_int (52))
                                                (Prims.of_int (22)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (50))
                                                (Prims.of_int (15))
                                                (Prims.of_int (52))
                                                (Prims.of_int (22)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (51))
                                                      (Prims.of_int (18))
                                                      (Prims.of_int (51))
                                                      (Prims.of_int (43)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Printf.fst"
                                                      (Prims.of_int (121))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (123))
                                                      (Prims.of_int (44)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Builtins.range_to_string
                                                   range))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     fun x ->
                                                       Prims.strcat
                                                         (Prims.strcat ""
                                                            (Prims.strcat
                                                               uu___1 ": "))
                                                         (Prims.strcat x "")))))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 -> uu___1 msg))))
                                 (fun uu___1 ->
                                    FStar_Tactics_V2_Derived.fail uu___1)))
                       uu___)
let _ =
  FStar_Tactics_Native.register_tactic "Pulse.Main.check_pulse"
    (Prims.of_int (8))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_V2_InterpFuns.mk_tactic_interpretation_7
             (FStar_Tactics_Native.from_tactic_7 check_pulse)
             (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string)
             (FStar_Syntax_Embeddings.e_list
                (FStar_Syntax_Embeddings.e_tuple2
                   FStar_Syntax_Embeddings.e_string
                   FStar_Syntax_Embeddings.e_string))
             FStar_Syntax_Embeddings.e_string
             FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_int
             FStar_Syntax_Embeddings.e_int
             FStar_Reflection_V2_Embeddings.e_env
             (FStar_Syntax_Embeddings.e_tuple2
                FStar_Reflection_V2_Embeddings.e_term
                FStar_Reflection_V2_Embeddings.e_term) psc ncb args)