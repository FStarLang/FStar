open Prims
let rec (readback_pat :
  FStar_Reflection_V2_Data.pattern ->
    Pulse_Syntax_Base.pattern FStar_Pervasives_Native.option)
  =
  fun p ->
    match p with
    | FStar_Reflection_V2_Data.Pat_Cons (fv, uu___, args) ->
        let fv1 = FStar_Reflection_V2_Builtins.inspect_fv fv in
        Pulse_Syntax_Pure.op_let_Question
          (Pulse_Common.map_opt_dec p readback_sub_pat args)
          (fun args1 ->
             FStar_Pervasives_Native.Some
               (Pulse_Syntax_Base.Pat_Cons
                  ({
                     Pulse_Syntax_Base.fv_name = fv1;
                     Pulse_Syntax_Base.fv_range = FStar_Range.range_0
                   }, args1)))
    | FStar_Reflection_V2_Data.Pat_Constant c ->
        FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Pat_Constant c)
    | FStar_Reflection_V2_Data.Pat_Var (st, nm) ->
        FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Pat_Var nm)
    | FStar_Reflection_V2_Data.Pat_Dot_Term (FStar_Pervasives_Native.None) ->
        FStar_Pervasives_Native.Some
          (Pulse_Syntax_Base.Pat_Dot_Term FStar_Pervasives_Native.None)
    | FStar_Reflection_V2_Data.Pat_Dot_Term (FStar_Pervasives_Native.Some t)
        ->
        if
          FStar_Reflection_V2_Data.uu___is_Tv_Unknown
            (FStar_Reflection_V2_Builtins.inspect_ln t)
        then FStar_Pervasives_Native.None
        else
          (let t1 = Pulse_Syntax_Base.tm_fstar t FStar_Range.range_0 in
           FStar_Pervasives_Native.Some
             (Pulse_Syntax_Base.Pat_Dot_Term
                (FStar_Pervasives_Native.Some t1)))
    | uu___ -> FStar_Pervasives_Native.None
and (readback_sub_pat :
  (FStar_Reflection_V2_Data.pattern * Prims.bool) ->
    (Pulse_Syntax_Base.pattern * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun pb ->
    let uu___ = pb in
    match uu___ with
    | (p, b) ->
        Pulse_Syntax_Pure.op_let_Question (readback_pat p)
          (fun p1 -> FStar_Pervasives_Native.Some (p1, b))

type ('b1, 'b2) samepat = unit
type ('bs1, 'bs2) samepats = unit
let (open_st_term_bs :
  Pulse_Syntax_Base.st_term ->
    Pulse_Typing_Env.binding Prims.list ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun bs ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   let rec aux bs1 i =
                     match bs1 with
                     | [] -> []
                     | b::bs2 ->
                         (Pulse_Syntax_Naming.DT
                            (i,
                              (Pulse_Syntax_Pure.term_of_nvar
                                 (Pulse_Syntax_Base.ppname_default,
                                   (FStar_Pervasives_Native.fst b)))))
                         :: (aux bs2 (i + Prims.int_one)) in
                   let ss = aux (FStar_List_Tot_Base.rev bs) Prims.int_zero in
                   Pulse_Syntax_Naming.subst_st_term t ss))) uu___1 uu___
let rec (r_bindings_to_string :
  FStar_Reflection_V2_Data.binding Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun bs ->
       match bs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | b::bs1 ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (188)) (Prims.of_int (4))
                            (Prims.of_int (188)) (Prims.of_int (90)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (188)) (Prims.of_int (4))
                            (Prims.of_int (188)) (Prims.of_int (116)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Match.fst"
                                  (Prims.of_int (188)) (Prims.of_int (5))
                                  (Prims.of_int (188)) (Prims.of_int (22)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Match.fst"
                                  (Prims.of_int (188)) (Prims.of_int (4))
                                  (Prims.of_int (188)) (Prims.of_int (90)))))
                         (Obj.magic
                            (FStar_Tactics_Unseal.unseal
                               b.FStar_Reflection_V2_Data.ppname3))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Match.fst"
                                             (Prims.of_int (188))
                                             (Prims.of_int (25))
                                             (Prims.of_int (188))
                                             (Prims.of_int (89)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Match.fst"
                                                   (Prims.of_int (188))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (188))
                                                   (Prims.of_int (89)))))
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
                                                         "Pulse.Checker.Match.fst"
                                                         (Prims.of_int (188))
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (188))
                                                         (Prims.of_int (89)))))
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
                                                               "Pulse.Checker.Match.fst"
                                                               (Prims.of_int (188))
                                                               (Prims.of_int (60))
                                                               (Prims.of_int (188))
                                                               (Prims.of_int (89)))))
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
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (83)))))
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
                                                                  b.FStar_Reflection_V2_Data.sort3))
                                                            (fun uu___1 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___2
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___1
                                                                    " "))))
                                                      (fun uu___1 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___2 ->
                                                              Prims.strcat
                                                                ":" uu___1))))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat
                                                          (Prims.string_of_int
                                                             b.FStar_Reflection_V2_Data.uniq1)
                                                          uu___1))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat "-" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Match.fst"
                                       (Prims.of_int (188))
                                       (Prims.of_int (93))
                                       (Prims.of_int (188))
                                       (Prims.of_int (116)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "prims.fst"
                                       (Prims.of_int (590))
                                       (Prims.of_int (19))
                                       (Prims.of_int (590))
                                       (Prims.of_int (31)))))
                              (Obj.magic (r_bindings_to_string bs1))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> Prims.strcat uu___ uu___1))))
                        uu___)))) uu___
let rec (bindings_to_string :
  Pulse_Typing_Env.binding Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun bs ->
       match bs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | b::bs1 ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (194)) (Prims.of_int (4))
                            (Prims.of_int (194)) (Prims.of_int (85)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (194)) (Prims.of_int (4))
                            (Prims.of_int (194)) (Prims.of_int (109)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Match.fst"
                                  (Prims.of_int (194)) (Prims.of_int (29))
                                  (Prims.of_int (194)) (Prims.of_int (84)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (590)) (Prims.of_int (19))
                                  (Prims.of_int (590)) (Prims.of_int (31)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Match.fst"
                                        (Prims.of_int (194))
                                        (Prims.of_int (35))
                                        (Prims.of_int (194))
                                        (Prims.of_int (84)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "prims.fst"
                                        (Prims.of_int (590))
                                        (Prims.of_int (19))
                                        (Prims.of_int (590))
                                        (Prims.of_int (31)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Match.fst"
                                              (Prims.of_int (194))
                                              (Prims.of_int (35))
                                              (Prims.of_int (194))
                                              (Prims.of_int (78)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range "prims.fst"
                                              (Prims.of_int (590))
                                              (Prims.of_int (19))
                                              (Prims.of_int (590))
                                              (Prims.of_int (31)))))
                                     (Obj.magic
                                        (Pulse_Syntax_Printer.term_to_string
                                           (FStar_Pervasives_Native.snd b)))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             Prims.strcat uu___ " "))))
                               (fun uu___ ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 -> Prims.strcat ":" uu___))))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Prims.strcat
                                   (Prims.string_of_int
                                      (FStar_Pervasives_Native.fst b)) uu___))))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Match.fst"
                                       (Prims.of_int (194))
                                       (Prims.of_int (88))
                                       (Prims.of_int (194))
                                       (Prims.of_int (109)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "prims.fst"
                                       (Prims.of_int (590))
                                       (Prims.of_int (19))
                                       (Prims.of_int (590))
                                       (Prims.of_int (31)))))
                              (Obj.magic (bindings_to_string bs1))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> Prims.strcat uu___ uu___1))))
                        uu___)))) uu___
let (check_branch :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Checker_Common.check_t ->
            Pulse_Syntax_Base.universe ->
              Pulse_Syntax_Base.typ ->
                Pulse_Syntax_Base.term ->
                  FStar_Reflection_V2_Data.pattern ->
                    Pulse_Syntax_Base.st_term ->
                      FStar_Reflection_V2_Data.binding Prims.list ->
                        ((Pulse_Syntax_Base.pattern,
                           Pulse_Syntax_Base.st_term,
                           Pulse_Syntax_Base.comp_st,
                           (unit, unit, unit, unit, unit, unit, unit)
                             Pulse_Typing.br_typing)
                           FStar_Pervasives.dtuple4,
                          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun check ->
            fun sc_u ->
              fun sc_ty ->
                fun sc ->
                  fun p0 ->
                    fun e ->
                      fun bs ->
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Match.fst"
                                   (Prims.of_int (215)) (Prims.of_int (10))
                                   (Prims.of_int (216)) (Prims.of_int (48)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Match.fst"
                                   (Prims.of_int (218)) (Prims.of_int (27))
                                   (Prims.of_int (242)) (Prims.of_int (58)))))
                          (match readback_pat p0 with
                           | FStar_Pervasives_Native.Some p ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ -> p)))
                           | FStar_Pervasives_Native.None ->
                               Obj.magic
                                 (Obj.repr
                                    (Pulse_Typing_Env.fail g
                                       (FStar_Pervasives_Native.Some
                                          (e.Pulse_Syntax_Base.range2))
                                       "readback_pat failed")))
                          (fun uu___ ->
                             (fun p ->
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Match.fst"
                                              (Prims.of_int (219))
                                              (Prims.of_int (17))
                                              (Prims.of_int (219))
                                              (Prims.of_int (42)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Match.fst"
                                              (Prims.of_int (221))
                                              (Prims.of_int (54))
                                              (Prims.of_int (242))
                                              (Prims.of_int (58)))))
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___ ->
                                           FStar_List_Tot_Base.map
                                             Pulse_Typing.readback_binding bs))
                                     (fun uu___ ->
                                        (fun pulse_bs ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Match.fst"
                                                         (Prims.of_int (222))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (222))
                                                         (Prims.of_int (35)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Match.fst"
                                                         (Prims.of_int (222))
                                                         (Prims.of_int (38))
                                                         (Prims.of_int (242))
                                                         (Prims.of_int (58)))))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___ ->
                                                      Pulse_Typing.push_bindings
                                                        g pulse_bs))
                                                (fun uu___ ->
                                                   (fun g' ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (24)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___ ->
                                                                 Pulse_Typing_Env.fresh
                                                                   g'))
                                                           (fun uu___ ->
                                                              (fun hyp_var ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Reflection_Typing.elaborate_pat
                                                                    p0 bs))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    elab_p ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                                    (if
                                                                    Prims.op_Negation
                                                                    (FStar_Pervasives_Native.uu___is_Some
                                                                    elab_p)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e.Pulse_Syntax_Base.range2))
                                                                    "Failed to elab pattern into term"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    uu___ ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                                    (if
                                                                    FStar_Reflection_V2_Data.uu___is_Tv_Unknown
                                                                    (FStar_Reflection_V2_Builtins.inspect_ln
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    elab_p)))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e.Pulse_Syntax_Base.range2))
                                                                    "should not happen: pattern elaborated to Tv_Unknown"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (77)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (76)))))
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
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    elab_p))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Elaborated pattern = "
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___2))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.mk_sq_eq2
                                                                    sc_u
                                                                    sc_ty sc
                                                                    (Pulse_Syntax_Base.tm_fstar
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    elab_p))
                                                                    FStar_Range.range_0)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    eq_typ ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (106)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g'
                                                                    hyp_var
                                                                    {
                                                                    Pulse_Syntax_Base.name
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "branch equality");
                                                                    Pulse_Syntax_Base.range
                                                                    =
                                                                    FStar_Range.range_0
                                                                    } eq_typ))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun g'1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (open_st_term_bs
                                                                    e
                                                                    pulse_bs))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun e1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    pre_typing2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (check
                                                                    g'1 pre
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    e1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.apply_checker_result_k
                                                                    g'1 pre
                                                                    post_hint
                                                                    r))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e2, c,
                                                                    e_d) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (58)))))
                                                                    (if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e2.Pulse_Syntax_Base.range2))
                                                                    "Branch computation is not stateful"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (p,
                                                                    (Pulse_Syntax_Naming.close_st_term_n
                                                                    e2
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.fst
                                                                    pulse_bs)),
                                                                    c,
                                                                    (Pulse_Typing.TBR
                                                                    (g, sc_u,
                                                                    sc_ty,
                                                                    sc, c, p,
                                                                    e2, bs,
                                                                    (), (),
                                                                    (),
                                                                    hyp_var,
                                                                    e_d)))))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                                    uu___)))
                                                                    uu___)))
                                                                uu___)))
                                                     uu___))) uu___))) uu___)
let (check_branches :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Checker_Common.check_t ->
            Pulse_Syntax_Base.universe ->
              Pulse_Syntax_Base.typ ->
                Pulse_Syntax_Base.term ->
                  Pulse_Syntax_Base.branch Prims.list ->
                    (FStar_Reflection_V2_Data.pattern *
                      FStar_Reflection_V2_Data.binding Prims.list) Prims.list
                      ->
                      ((Pulse_Syntax_Base.branch Prims.list,
                         Pulse_Syntax_Base.comp_st,
                         (unit, unit, unit, unit, unit, unit)
                           Pulse_Typing.brs_typing)
                         FStar_Pervasives.dtuple3,
                        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun check ->
            fun sc_u ->
              fun sc_ty ->
                fun sc ->
                  fun brs0 ->
                    fun bnds ->
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                                 (Prims.of_int (258)) (Prims.of_int (2))
                                 (Prims.of_int (258)) (Prims.of_int (50)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                                 (Prims.of_int (258)) (Prims.of_int (51))
                                 (Prims.of_int (291)) (Prims.of_int (18)))))
                        (if FStar_List_Tot_Base.isEmpty brs0
                         then
                           Obj.magic
                             (Obj.repr
                                (Pulse_Typing_Env.fail g
                                   FStar_Pervasives_Native.None "empty match"))
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
                                            "Pulse.Checker.Match.fst"
                                            (Prims.of_int (259))
                                            (Prims.of_int (22))
                                            (Prims.of_int (259))
                                            (Prims.of_int (26)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Match.fst"
                                            (Prims.of_int (258))
                                            (Prims.of_int (51))
                                            (Prims.of_int (291))
                                            (Prims.of_int (18)))))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 -> brs0))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         match uu___1 with
                                         | (uu___2, e0)::rest ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Match.fst"
                                                           (Prims.of_int (260))
                                                           (Prims.of_int (26))
                                                           (Prims.of_int (260))
                                                           (Prims.of_int (30)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Match.fst"
                                                           (Prims.of_int (259))
                                                           (Prims.of_int (29))
                                                           (Prims.of_int (291))
                                                           (Prims.of_int (18)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 -> bnds))
                                                  (fun uu___3 ->
                                                     (fun uu___3 ->
                                                        match uu___3 with
                                                        | (p0, bnds0)::bnds1
                                                            ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (100)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (18)))))
                                                                 (Obj.magic
                                                                    (
                                                                    check_branch
                                                                    g pre ()
                                                                    post_hint
                                                                    check
                                                                    sc_u
                                                                    sc_ty sc
                                                                    p0 e0
                                                                    bnds0))
                                                                 (fun uu___4
                                                                    ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (p01,
                                                                    e01, c0,
                                                                    d0) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun b ->
                                                                    fun pbs
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    b))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (uu___7,
                                                                    e) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    pbs))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (p, bs)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    g pre ()
                                                                    post_hint
                                                                    check
                                                                    sc_u
                                                                    sc_ty sc
                                                                    p e bs))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (p1, e1,
                                                                    c, d) ->
                                                                    Prims.Mkdtuple2
                                                                    ((p1, e1),
                                                                    d)))))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun tr1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (Pulse_Common.zipWith
                                                                    tr1 rest
                                                                    bnds1))
                                                                    (fun r ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    r))))
                                                                    uu___5)))
                                                                    (fun
                                                                    brs_d ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((FStar_List_Tot_Base.map
                                                                    FStar_Pervasives.dfst
                                                                    brs_d),
                                                                    c0,
                                                                    (let rec aux
                                                                    brs =
                                                                    match brs
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Pulse_Typing.TBRS_0
                                                                    c0
                                                                    | 
                                                                    (Prims.Mkdtuple2
                                                                    ((p, e),
                                                                    d))::rest1
                                                                    ->
                                                                    Pulse_Typing.TBRS_1
                                                                    (c0, p,
                                                                    e, d,
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives.dfst
                                                                    rest1),
                                                                    (aux
                                                                    rest1)) in
                                                                    aux brs_d))))))
                                                                    uu___4)))
                                                       uu___3))) uu___1)))
                             uu___)
let (check_match :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.branch Prims.list ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Typing.post_hint_for_env ->
              Pulse_Checker_Common.check_t ->
                ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun sc ->
      fun brs ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun check ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                           (Prims.of_int (303)) (Prims.of_int (17))
                           (Prims.of_int (303)) (Prims.of_int (25)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                           (Prims.of_int (303)) (Prims.of_int (28))
                           (Prims.of_int (349)) (Prims.of_int (44)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> sc.Pulse_Syntax_Base.range1))
                  (fun uu___ ->
                     (fun sc_range ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Match.fst"
                                      (Prims.of_int (304))
                                      (Prims.of_int (17))
                                      (Prims.of_int (304))
                                      (Prims.of_int (20)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Match.fst"
                                      (Prims.of_int (304))
                                      (Prims.of_int (23))
                                      (Prims.of_int (349))
                                      (Prims.of_int (44)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> brs))
                             (fun uu___ ->
                                (fun orig_brs ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Match.fst"
                                                 (Prims.of_int (305))
                                                 (Prims.of_int (12))
                                                 (Prims.of_int (305))
                                                 (Prims.of_int (24)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Match.fst"
                                                 (Prims.of_int (305))
                                                 (Prims.of_int (27))
                                                 (Prims.of_int (349))
                                                 (Prims.of_int (44)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___ ->
                                              FStar_List_Tot_Base.length brs))
                                        (fun uu___ ->
                                           (fun nbr ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Match.fst"
                                                            (Prims.of_int (307))
                                                            (Prims.of_int (55))
                                                            (Prims.of_int (307))
                                                            (Prims.of_int (79)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Match.fst"
                                                            (Prims.of_int (305))
                                                            (Prims.of_int (27))
                                                            (Prims.of_int (349))
                                                            (Prims.of_int (44)))))
                                                   (Obj.magic
                                                      (Pulse_Checker_Pure.check_term_and_type
                                                         g sc))
                                                   (fun uu___ ->
                                                      (fun uu___ ->
                                                         match uu___ with
                                                         | FStar_Pervasives.Mkdtuple5
                                                             (sc1, sc_u,
                                                              sc_ty,
                                                              sc_ty_typing,
                                                              sc_typing)
                                                             ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (48)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (44)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_List_Tot_Base.map
                                                                    Pulse_Elaborate_Pure.elab_pat
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.fst
                                                                    brs)))
                                                                  (fun uu___1
                                                                    ->
                                                                    (fun
                                                                    elab_pats
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.check_match_complete
                                                                    (Pulse_Typing.elab_env
                                                                    g)
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    sc1)
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    sc_ty)
                                                                    elab_pats))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    sc_range)
                                                                    "Could not check that match is correct/complete"))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (elab_pats',
                                                                    bnds) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (elab_pats',
                                                                    bnds,
                                                                    (Pulse_Typing.PC_Elab
                                                                    (g, sc1,
                                                                    sc_ty,
                                                                    elab_pats',
                                                                    bnds,
                                                                    (FStar_Reflection_Typing.MC_Tok
                                                                    ((Pulse_Typing.elab_env
                                                                    g),
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    sc1),
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    sc_ty),
                                                                    elab_pats',
                                                                    bnds, ())))))))))
                                                                    uu___1)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (elab_pats',
                                                                    bnds',
                                                                    complete_d)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    uu___1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Common.map_opt
                                                                    readback_pat
                                                                    elab_pats'))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    new_pats
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (44)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    new_pats
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    sc_range)
                                                                    "failed to readback new patterns"))
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
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Common.zipWith
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun
                                                                    uu___4 ->
                                                                    (fun p ->
                                                                    fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (uu___6,
                                                                    e) ->
                                                                    (p, e))))
                                                                    uu___5
                                                                    uu___4)
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    new_pats)
                                                                    brs))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun brs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (116)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (check_branches
                                                                    g pre ()
                                                                    post_hint
                                                                    check
                                                                    sc_u
                                                                    sc_ty sc1
                                                                    brs1
                                                                    (Pulse_Common.zip
                                                                    elab_pats'
                                                                    bnds')))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (brs2, c,
                                                                    brs_d) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_Match
                                                                    (g, sc_u,
                                                                    sc_ty,
                                                                    sc1, (),
                                                                    (), c,
                                                                    brs2,
                                                                    brs_d,
                                                                    complete_d)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.checker_result_for_st_typing
                                                                    g pre
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Match
                                                                    {
                                                                    Pulse_Syntax_Base.sc
                                                                    = sc1;
                                                                    Pulse_Syntax_Base.returns_
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.brs
                                                                    = brs2
                                                                    })), c,
                                                                    d))))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                        uu___))) uu___)))
                                  uu___))) uu___)