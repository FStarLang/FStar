open Prims
let (debug_main :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun s ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "pulse.main"
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (36)) (Prims.of_int (15))
                              (Prims.of_int (36)) (Prims.of_int (21)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (36)) (Prims.of_int (7))
                              (Prims.of_int (36)) (Prims.of_int (21)))))
                     (Obj.magic (s ()))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___))
                          uu___)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let rec (mk_abs :
  Pulse_Typing_Env.env ->
    (Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option *
      Pulse_Syntax_Base.binder * Pulse_Syntax_Base.bv) Prims.list ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp ->
          (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun qbs ->
      fun body ->
        fun comp ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (44))
                     (Prims.of_int (6)) (Prims.of_int (44))
                     (Prims.of_int (59)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (46))
                     (Prims.of_int (2)) (Prims.of_int (55))
                     (Prims.of_int (81)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  fun s ->
                    fun r ->
                      {
                        Pulse_Syntax_Base.term1 = s;
                        Pulse_Syntax_Base.range1 = r;
                        Pulse_Syntax_Base.effect_tag =
                          Pulse_Syntax_Base.default_effect_hint
                      }))
            (fun uu___ ->
               (fun with_range ->
                  match qbs with
                  | (q, last, last_bv)::[] ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ ->
                                 with_range
                                   (Pulse_Syntax_Builder.tm_abs last q
                                      {
                                        Pulse_Syntax_Base.annotated =
                                          (FStar_Pervasives_Native.Some
                                             (Pulse_Syntax_Naming.close_comp
                                                comp
                                                last_bv.Pulse_Syntax_Base.bv_index));
                                        Pulse_Syntax_Base.elaborated =
                                          FStar_Pervasives_Native.None
                                      }
                                      (Pulse_Syntax_Naming.close_st_term body
                                         last_bv.Pulse_Syntax_Base.bv_index))
                                   (Pulse_Syntax_Naming.close_st_term body
                                      last_bv.Pulse_Syntax_Base.bv_index).Pulse_Syntax_Base.range1)))
                  | (q, b, bv)::qbs1 ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Main.fst"
                                       (Prims.of_int (53))
                                       (Prims.of_int (15))
                                       (Prims.of_int (53))
                                       (Prims.of_int (37)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Main.fst"
                                       (Prims.of_int (55)) (Prims.of_int (4))
                                       (Prims.of_int (55))
                                       (Prims.of_int (81)))))
                              (Obj.magic (mk_abs g qbs1 body comp))
                              (fun body1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      with_range
                                        (Pulse_Syntax_Builder.tm_abs b q
                                           Pulse_Syntax_Base.empty_ascription
                                           (Pulse_Syntax_Naming.close_st_term
                                              body1
                                              bv.Pulse_Syntax_Base.bv_index))
                                        (Pulse_Syntax_Naming.close_st_term
                                           body1
                                           bv.Pulse_Syntax_Base.bv_index).Pulse_Syntax_Base.range1)))))
                 uu___)
let (check_fndecl :
  Pulse_Syntax_Base.decl ->
    Pulse_Soundness_Common.stt_env ->
      Pulse_Syntax_Base.term ->
        unit ->
          (unit FStar_Reflection_Typing.dsl_tac_result_t, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    fun g ->
      fun pre ->
        fun pre_typing ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (65))
                     (Prims.of_int (20)) (Prims.of_int (65))
                     (Prims.of_int (23)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (62))
                     Prims.int_one (Prims.of_int (125)) (Prims.of_int (30)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> d.Pulse_Syntax_Base.d))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | Pulse_Syntax_Base.FnDecl fn_d ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (66)) (Prims.of_int (16))
                                    (Prims.of_int (66)) (Prims.of_int (43)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (66)) (Prims.of_int (46))
                                    (Prims.of_int (125)) (Prims.of_int (30)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 FStar_Pervasives_Native.fst
                                   (FStar_Reflection_V2_Builtins.inspect_ident
                                      fn_d.Pulse_Syntax_Base.id)))
                           (fun uu___1 ->
                              (fun nm_orig ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (68))
                                               (Prims.of_int (4))
                                               (Prims.of_int (70))
                                               (Prims.of_int (10)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (71))
                                               (Prims.of_int (4))
                                               (Prims.of_int (125))
                                               (Prims.of_int (30)))))
                                      (if fn_d.Pulse_Syntax_Base.isrec
                                       then
                                         Obj.magic
                                           (Obj.repr
                                              (Pulse_Recursion.add_knot g
                                                 d.Pulse_Syntax_Base.range2 d))
                                       else
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 -> d))))
                                      (fun uu___1 ->
                                         (fun d1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (73))
                                                          (Prims.of_int (51))
                                                          (Prims.of_int (73))
                                                          (Prims.of_int (54)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (71))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (125))
                                                          (Prims.of_int (30)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       d1.Pulse_Syntax_Base.d))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       match uu___1 with
                                                       | Pulse_Syntax_Base.FnDecl
                                                           {
                                                             Pulse_Syntax_Base.id
                                                               = id;
                                                             Pulse_Syntax_Base.isrec
                                                               = isrec;
                                                             Pulse_Syntax_Base.bs
                                                               = bs;
                                                             Pulse_Syntax_Base.comp
                                                               = comp;
                                                             Pulse_Syntax_Base.meas
                                                               = meas;
                                                             Pulse_Syntax_Base.body7
                                                               = body;_}
                                                           ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (37)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives_Native.fst
                                                                    (FStar_Reflection_V2_Builtins.inspect_ident
                                                                    id)))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    nm_aux ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (if
                                                                    Prims.uu___is_Nil
                                                                    bs
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (d1.Pulse_Syntax_Base.range2))
                                                                    "main: FnDecl does not have binders"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (mk_abs g
                                                                    bs body
                                                                    comp))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    body1.Pulse_Syntax_Base.range1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun rng
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (debug_main
                                                                    g
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (95)))))
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
                                                                    body1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "\nbody after mk_abs:\n"
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Abs.check_abs
                                                                    g body1
                                                                    Pulse_Checker.check))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body2,
                                                                    c,
                                                                    t_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    g
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    body2))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "\ncheck call returned in main with:\n"
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    "\nat type "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    uu___6))))
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (debug_main
                                                                    g
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Printer.print_st_typing
                                                                    g body2 c
                                                                    t_typing))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    body2))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "\nchecker call returned in main with:\n"
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\nderivation="))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8
                                                                    uu___7))))
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Elaborate_Pure.elab_comp
                                                                    c))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    refl_t ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_RuntimeUtils.embed_st_term_for_extraction
                                                                    body2
                                                                    (FStar_Pervasives_Native.Some
                                                                    rng)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    refl_e ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ("pulse",
                                                                    refl_e)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun blob
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.fst
                                                                    (FStar_Reflection_V2_Builtins.inspect_ident
                                                                    id)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun nm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (94)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.ext_getv
                                                                    "pulse:elab_derivation"))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7 <>
                                                                    ""))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    if uu___7
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Reflection_Typing.mk_checked_let
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g) nm
                                                                    (Pulse_Elaborate_Core.elab_st_typing
                                                                    g body2 c
                                                                    t_typing)
                                                                    refl_t)
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Reflection_Util.mk_opaque_let
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g) nm ()
                                                                    refl_t))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    main_decl
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match main_decl
                                                                    with
                                                                    | 
                                                                    (chk, se,
                                                                    uu___8)
                                                                    ->
                                                                    (chk,
                                                                    (if
                                                                    fn_d.Pulse_Syntax_Base.isrec
                                                                    then
                                                                    Pulse_RuntimeUtils.add_attribute
                                                                    (Pulse_RuntimeUtils.add_noextract_qual
                                                                    (Pulse_RuntimeUtils.add_attribute
                                                                    se
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "noextract_to"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    "krml"))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))))
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    "pulse.recursive"))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    nm_orig))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))
                                                                    else se),
                                                                    (FStar_Pervasives_Native.Some
                                                                    blob))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    main_decl1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (30)))))
                                                                    (if
                                                                    fn_d.Pulse_Syntax_Base.isrec
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Recursion.tie_knot
                                                                    g rng
                                                                    nm_orig
                                                                    nm_aux d1
                                                                    refl_t
                                                                    blob))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    []))))
                                                                    (fun
                                                                    recursive_decls
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    main_decl1
                                                                    ::
                                                                    recursive_decls))))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                      uu___1))) uu___1)))
                                uu___1))) uu___)
let (main' :
  Prims.string ->
    Pulse_Syntax_Base.decl ->
      Pulse_Syntax_Base.term ->
        FStar_Reflection_Typing.fstar_top_env ->
          (unit FStar_Reflection_Typing.dsl_tac_result_t, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun nm ->
             fun d ->
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
                                        (Prims.of_int (132))
                                        (Prims.of_int (6))
                                        (Prims.of_int (133))
                                        (Prims.of_int (88)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.Main.fst"
                                        (Prims.of_int (133))
                                        (Prims.of_int (89))
                                        (Prims.of_int (140))
                                        (Prims.of_int (39)))))
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
                                                   (Prims.of_int (133))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (133))
                                                   (Prims.of_int (88)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (133))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (133))
                                                   (Prims.of_int (88)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Main.fst"
                                                         (Prims.of_int (133))
                                                         (Prims.of_int (67))
                                                         (Prims.of_int (133))
                                                         (Prims.of_int (87)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (Pulse_Syntax_Printer.decl_to_string
                                                      d))
                                                (fun uu___ ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 ->
                                                        Prims.strcat
                                                          "About to check pulse decl:\n"
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
                                                   (Prims.of_int (134))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (134))
                                                   (Prims.of_int (84)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (133))
                                                   (Prims.of_int (89))
                                                   (Prims.of_int (140))
                                                   (Prims.of_int (39)))))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.compute_tot_term_type
                                                g1 pre))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (pre1, ty, pre_typing) ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (135))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (136))
                                                                  (Prims.of_int (109)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (136))
                                                                  (Prims.of_int (110))
                                                                  (Prims.of_int (140))
                                                                  (Prims.of_int (39)))))
                                                         (if
                                                            Prims.op_Negation
                                                              (Pulse_Syntax_Base.eq_tm
                                                                 ty
                                                                 Pulse_Syntax_Pure.tm_vprop)
                                                          then
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    pre1))
                                                                    "pulse main: cannot typecheck pre at type vprop"))
                                                          else
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    ()))))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (61)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (39)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    match 
                                                                    d.Pulse_Syntax_Base.d
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.FnDecl
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (check_fndecl
                                                                    d g1 pre1
                                                                    ()))
                                                                    uu___3)))
                                                              uu___2)))
                                               uu___1))) uu___)))) uu___3
            uu___2 uu___1 uu___
let (join_smt_goals : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (146))
               (Prims.of_int (2)) (Prims.of_int (147)) (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (147))
               (Prims.of_int (36)) (Prims.of_int (168)) (Prims.of_int (4)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (146))
                     (Prims.of_int (5)) (Prims.of_int (146))
                     (Prims.of_int (48)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (146))
                     (Prims.of_int (2)) (Prims.of_int (147))
                     (Prims.of_int (35)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (146)) (Prims.of_int (23))
                           (Prims.of_int (146)) (Prims.of_int (35)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (146)) (Prims.of_int (5))
                           (Prims.of_int (146)) (Prims.of_int (48)))))
                  (Obj.magic (FStar_Tactics_V2_Builtins.top_env ()))
                  (fun uu___1 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 ->
                          Pulse_RuntimeUtils.debug_at_level uu___1
                            "pulse.join"))))
            (fun uu___1 ->
               (fun uu___1 ->
                  if uu___1
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_V2_Builtins.dump
                            "PULSE: Goals before join"))
                  else
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> ())))) uu___1)))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (150)) (Prims.of_int (18))
                          (Prims.of_int (150)) (Prims.of_int (30)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (151)) (Prims.of_int (2))
                          (Prims.of_int (168)) (Prims.of_int (4)))))
                 (Obj.magic (FStar_Tactics_V2_Derived.smt_goals ()))
                 (fun uu___2 ->
                    (fun smt_goals ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (151)) (Prims.of_int (2))
                                     (Prims.of_int (151)) (Prims.of_int (34)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (152)) (Prims.of_int (2))
                                     (Prims.of_int (168)) (Prims.of_int (4)))))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (151))
                                           (Prims.of_int (12))
                                           (Prims.of_int (151))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (151))
                                           (Prims.of_int (2))
                                           (Prims.of_int (151))
                                           (Prims.of_int (34)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (151))
                                                 (Prims.of_int (13))
                                                 (Prims.of_int (151))
                                                 (Prims.of_int (21)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (151))
                                                 (Prims.of_int (12))
                                                 (Prims.of_int (151))
                                                 (Prims.of_int (34)))))
                                        (Obj.magic
                                           (FStar_Tactics_V2_Derived.goals ()))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                FStar_List_Tot_Base.op_At
                                                  uu___2 smt_goals))))
                                  (fun uu___2 ->
                                     (fun uu___2 ->
                                        Obj.magic
                                          (FStar_Tactics_V2_Builtins.set_goals
                                             uu___2)) uu___2)))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (152))
                                                (Prims.of_int (2))
                                                (Prims.of_int (152))
                                                (Prims.of_int (18)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (152))
                                                (Prims.of_int (19))
                                                (Prims.of_int (168))
                                                (Prims.of_int (4)))))
                                       (Obj.magic
                                          (FStar_Tactics_V2_Builtins.set_smt_goals
                                             []))
                                       (fun uu___3 ->
                                          (fun uu___3 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (153))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (153))
                                                           (Prims.of_int (36)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (154))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (168))
                                                           (Prims.of_int (4)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (153))
                                                                 (Prims.of_int (26))
                                                                 (Prims.of_int (153))
                                                                 (Prims.of_int (36)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (153))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (153))
                                                                 (Prims.of_int (36)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Derived.goals
                                                              ()))
                                                        (fun uu___4 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___5 ->
                                                                FStar_List_Tot_Base.length
                                                                  uu___4))))
                                                  (fun uu___4 ->
                                                     (fun n ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (22)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (4)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (22)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (22)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.repeat
                                                                    FStar_Tactics_V2_Builtins.join))
                                                                   (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))))
                                                             (fun uu___4 ->
                                                                (fun uu___4
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (4)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.goals
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.uu___is_Nil
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.op_Negation
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    if uu___5
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_SMT.get_rlimit
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6 +
                                                                    ((n -
                                                                    Prims.int_one)
                                                                    *
                                                                    (Prims.of_int (2)))))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    rlimit ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_SMT.set_rlimit
                                                                    rlimit))
                                                                    uu___6)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ()))))
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
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (4)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.top_env
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    uu___6
                                                                    "pulse.join"))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Builtins.dump
                                                                    "PULSE: Goals after join"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ()))))
                                                                    uu___5)))
                                                                  uu___4)))
                                                       uu___4))) uu___3)))
                                 uu___2))) uu___2))) uu___1)
let (main :
  Prims.string ->
    Pulse_Syntax_Base.decl ->
      Pulse_Syntax_Base.term -> FStar_Reflection_Typing.dsl_tac_t)
  =
  fun nm ->
    fun t ->
      fun pre ->
        fun g ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (175))
                     (Prims.of_int (2)) (Prims.of_int (178))
                     (Prims.of_int (24)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (178))
                     (Prims.of_int (25)) (Prims.of_int (187))
                     (Prims.of_int (5)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (175)) (Prims.of_int (5))
                           (Prims.of_int (175)) (Prims.of_int (46)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (175)) (Prims.of_int (2))
                           (Prims.of_int (178)) (Prims.of_int (24)))))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Main.fst"
                                 (Prims.of_int (175)) (Prims.of_int (5))
                                 (Prims.of_int (175)) (Prims.of_int (34)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Main.fst"
                                 (Prims.of_int (175)) (Prims.of_int (5))
                                 (Prims.of_int (175)) (Prims.of_int (46)))))
                        (Obj.magic
                           (FStar_Tactics_V2_Builtins.ext_getv
                              "pulse:guard_policy"))
                        (fun uu___ ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 -> uu___ = "SMTSync"))))
                  (fun uu___ ->
                     (fun uu___ ->
                        if uu___
                        then
                          Obj.magic
                            (FStar_Tactics_V2_Builtins.set_guard_policy
                               FStar_Tactics_Types.SMTSync)
                        else
                          Obj.magic
                            (FStar_Tactics_V2_Builtins.set_guard_policy
                               FStar_Tactics_Types.SMT)) uu___)))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (180)) (Prims.of_int (12))
                                (Prims.of_int (180)) (Prims.of_int (28)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (182)) (Prims.of_int (2))
                                (Prims.of_int (187)) (Prims.of_int (5)))))
                       (Obj.magic (main' nm t pre g))
                       (fun uu___1 ->
                          (fun res ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (182))
                                           (Prims.of_int (2))
                                           (Prims.of_int (186))
                                           (Prims.of_int (20)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (180))
                                           (Prims.of_int (6))
                                           (Prims.of_int (180))
                                           (Prims.of_int (9)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (182))
                                                 (Prims.of_int (5))
                                                 (Prims.of_int (182))
                                                 (Prims.of_int (32)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (182))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (186))
                                                 (Prims.of_int (20)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Main.fst"
                                                       (Prims.of_int (182))
                                                       (Prims.of_int (5))
                                                       (Prims.of_int (182))
                                                       (Prims.of_int (26)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Main.fst"
                                                       (Prims.of_int (182))
                                                       (Prims.of_int (5))
                                                       (Prims.of_int (182))
                                                       (Prims.of_int (32)))))
                                              (Obj.magic
                                                 (FStar_Tactics_V2_Builtins.ext_getv
                                                    "pulse:join"))
                                              (fun uu___1 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      uu___1 = "1"))))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              if uu___1
                                              then
                                                Obj.magic
                                                  (Obj.repr
                                                     (join_smt_goals ()))
                                              else
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 -> ()))))
                                             uu___1)))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> res)))) uu___1))) uu___)
let (check_pulse :
  Prims.string Prims.list ->
    (Prims.string * Prims.string) Prims.list ->
      Prims.string ->
        Prims.string ->
          Prims.int ->
            Prims.int -> Prims.string -> FStar_Reflection_Typing.dsl_tac_t)
  =
  fun namespaces ->
    fun module_abbrevs ->
      fun content ->
        fun file_name ->
          fun line ->
            fun col ->
              fun nm ->
                fun env ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Main.fst"
                             (Prims.of_int (198)) (Prims.of_int (12))
                             (Prims.of_int (198)) (Prims.of_int (112)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Main.fst"
                             (Prims.of_int (198)) (Prims.of_int (6))
                             (Prims.of_int (214)) (Prims.of_int (36)))))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          PulseSyntaxExtension_ASTBuilder.parse_pulse env
                            namespaces module_abbrevs content file_name line
                            col))
                    (fun uu___ ->
                       (fun uu___ ->
                          match uu___ with
                          | FStar_Pervasives.Inl decl ->
                              Obj.magic
                                (Obj.repr
                                   (main nm decl Pulse_Syntax_Pure.tm_emp env))
                          | FStar_Pervasives.Inr
                              (FStar_Pervasives_Native.None) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_V2_Derived.fail
                                      "Pulse parser failed"))
                          | FStar_Pervasives.Inr
                              (FStar_Pervasives_Native.Some (msg, range)) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (207))
                                               (Prims.of_int (10))
                                               (Prims.of_int (211))
                                               (Prims.of_int (21)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (213))
                                               (Prims.of_int (8))
                                               (Prims.of_int (214))
                                               (Prims.of_int (36)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Main.fst"
                                                     (Prims.of_int (208))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (208))
                                                     (Prims.of_int (74)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Issue.fsti"
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (65)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (208))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (208))
                                                           (Prims.of_int (74)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (208))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (208))
                                                           (Prims.of_int (74)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (208))
                                                                 (Prims.of_int (44))
                                                                 (Prims.of_int (208))
                                                                 (Prims.of_int (69)))))
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
                                                              range))
                                                        (fun uu___1 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                fun x ->
                                                                  Prims.strcat
                                                                    (
                                                                    Prims.strcat
                                                                    ""
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    ": "))
                                                                    (
                                                                    Prims.strcat
                                                                    x "")))))
                                                  (fun uu___1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          uu___1 msg))))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    FStar_Issue.mk_issue_doc
                                                      "Error"
                                                      [FStar_Pprint.arbitrary_string
                                                         uu___1]
                                                      (FStar_Pervasives_Native.Some
                                                         range)
                                                      FStar_Pervasives_Native.None
                                                      []))))
                                      (fun uu___1 ->
                                         (fun i ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (213))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (213))
                                                          (Prims.of_int (24)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (214))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (214))
                                                          (Prims.of_int (36)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_V2_Builtins.log_issues
                                                       [i]))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_V2_Derived.fail
                                                      "Pulse parser failed")))
                                           uu___1)))) uu___)
let _ =
  FStar_Tactics_Native.register_tactic "Pulse.Main.check_pulse"
    (Prims.of_int (9))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_8
               "Pulse.Main.check_pulse (plugin)"
               (FStar_Tactics_Native.from_tactic_8 check_pulse)
               (FStar_Syntax_Embeddings.e_list
                  FStar_Syntax_Embeddings.e_string)
               (FStar_Syntax_Embeddings.e_list
                  (FStar_Syntax_Embeddings.e_tuple2
                     FStar_Syntax_Embeddings.e_string
                     FStar_Syntax_Embeddings.e_string))
               FStar_Syntax_Embeddings.e_string
               FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_int
               FStar_Syntax_Embeddings.e_int FStar_Syntax_Embeddings.e_string
               FStar_Reflection_V2_Embeddings.e_env
               (FStar_Syntax_Embeddings.e_list
                  (FStar_Syntax_Embeddings.e_tuple3
                     FStar_Syntax_Embeddings.e_bool
                     FStar_Reflection_V2_Embeddings.e_sigelt
                     (FStar_Syntax_Embeddings.e_option
                        (FStar_Syntax_Embeddings.e_tuple2
                           FStar_Syntax_Embeddings.e_string
                           FStar_Reflection_V2_Embeddings.e_term)))) psc ncb
               us args)