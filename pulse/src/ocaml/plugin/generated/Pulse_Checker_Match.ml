open Prims
let rec (readback_pat :
  FStarC_Reflection_V2_Data.pattern ->
    Pulse_Syntax_Base.pattern FStar_Pervasives_Native.option)
  =
  fun p ->
    match p with
    | FStarC_Reflection_V2_Data.Pat_Cons (fv, uu___, args) ->
        let fv1 = FStarC_Reflection_V2_Builtins.inspect_fv fv in
        Pulse_Syntax_Pure.op_let_Question
          (Pulse_Common.map_opt_dec p readback_sub_pat args)
          (fun args1 ->
             FStar_Pervasives_Native.Some
               (Pulse_Syntax_Base.Pat_Cons
                  ({
                     Pulse_Syntax_Base.fv_name = fv1;
                     Pulse_Syntax_Base.fv_range = FStar_Range.range_0
                   }, args1)))
    | FStarC_Reflection_V2_Data.Pat_Constant c ->
        FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Pat_Constant c)
    | FStarC_Reflection_V2_Data.Pat_Var (st, nm) ->
        FStar_Pervasives_Native.Some
          (Pulse_Syntax_Base.Pat_Var
             (nm,
               (Pulse_RuntimeUtils.map_seal st
                  Pulse_RuntimeUtils.deep_compress)))
    | FStarC_Reflection_V2_Data.Pat_Dot_Term (FStar_Pervasives_Native.None)
        ->
        FStar_Pervasives_Native.Some
          (Pulse_Syntax_Base.Pat_Dot_Term FStar_Pervasives_Native.None)
    | FStarC_Reflection_V2_Data.Pat_Dot_Term (FStar_Pervasives_Native.Some t)
        ->
        if
          FStarC_Reflection_V2_Data.uu___is_Tv_Unknown
            (FStarC_Reflection_V2_Builtins.inspect_ln t)
        then FStar_Pervasives_Native.None
        else
          (let t1 = Pulse_RuntimeUtils.deep_compress t in
           let t2 = Pulse_Syntax_Pure.wr t1 FStar_Range.range_0 in
           FStar_Pervasives_Native.Some
             (Pulse_Syntax_Base.Pat_Dot_Term
                (FStar_Pervasives_Native.Some t2)))
    | uu___ -> FStar_Pervasives_Native.None
and (readback_sub_pat :
  (FStarC_Reflection_V2_Data.pattern * Prims.bool) ->
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
    Pulse_Typing_Env.binding Prims.list -> Pulse_Syntax_Base.st_term)
  =
  fun t ->
    fun bs ->
      let rec aux bs1 i =
        match bs1 with
        | [] -> []
        | b::bs2 ->
            (FStar_Reflection_Typing.DT
               (i,
                 (Pulse_Syntax_Pure.term_of_nvar
                    (Pulse_Syntax_Base.ppname_default,
                      (FStar_Pervasives_Native.fst b)))))
            :: (aux bs2 (i + Prims.int_one)) in
      let ss = aux (FStar_List_Tot_Base.rev bs) Prims.int_zero in
      Pulse_Syntax_Naming.subst_st_term t ss
let rec (r_bindings_to_string :
  FStarC_Reflection_V2_Data.binding Prims.list ->
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
                (let uu___ =
                   let uu___1 =
                     FStarC_Tactics_Unseal.unseal
                       b.FStarC_Reflection_V2_Data.ppname3 in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                              (Prims.of_int (206)) (Prims.of_int (5))
                              (Prims.of_int (206)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                              (Prims.of_int (206)) (Prims.of_int (4))
                              (Prims.of_int (206)) (Prims.of_int (90)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 =
                                     FStarC_Tactics_V2_Builtins.term_to_string
                                       b.FStarC_Reflection_V2_Data.sort3 in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Match.fst"
                                              (Prims.of_int (206))
                                              (Prims.of_int (60))
                                              (Prims.of_int (206))
                                              (Prims.of_int (83)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range "Prims.fst"
                                              (Prims.of_int (611))
                                              (Prims.of_int (19))
                                              (Prims.of_int (611))
                                              (Prims.of_int (31)))))
                                     (Obj.magic uu___7)
                                     (fun uu___8 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___9 ->
                                             Prims.strcat uu___8 " ")) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Match.fst"
                                            (Prims.of_int (206))
                                            (Prims.of_int (60))
                                            (Prims.of_int (206))
                                            (Prims.of_int (89)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Prims.fst"
                                            (Prims.of_int (611))
                                            (Prims.of_int (19))
                                            (Prims.of_int (611))
                                            (Prims.of_int (31)))))
                                   (Obj.magic uu___6)
                                   (fun uu___7 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___8 ->
                                           Prims.strcat ":" uu___7)) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Match.fst"
                                          (Prims.of_int (206))
                                          (Prims.of_int (54))
                                          (Prims.of_int (206))
                                          (Prims.of_int (89)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 ->
                                         Prims.strcat
                                           (Prims.string_of_int
                                              b.FStarC_Reflection_V2_Data.uniq1)
                                           uu___6)) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Match.fst"
                                        (Prims.of_int (206))
                                        (Prims.of_int (31))
                                        (Prims.of_int (206))
                                        (Prims.of_int (89)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> Prims.strcat "-" uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Match.fst"
                                         (Prims.of_int (206))
                                         (Prims.of_int (25))
                                         (Prims.of_int (206))
                                         (Prims.of_int (89)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        Prims.strcat uu___2 uu___4)))) uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (206)) (Prims.of_int (4))
                            (Prims.of_int (206)) (Prims.of_int (90)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (206)) (Prims.of_int (4))
                            (Prims.of_int (206)) (Prims.of_int (116)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun uu___1 ->
                         let uu___2 = r_bindings_to_string bs1 in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Match.fst"
                                       (Prims.of_int (206))
                                       (Prims.of_int (93))
                                       (Prims.of_int (206))
                                       (Prims.of_int (116)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Prims.fst"
                                       (Prims.of_int (611))
                                       (Prims.of_int (19))
                                       (Prims.of_int (611))
                                       (Prims.of_int (31)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___4 -> Prims.strcat uu___1 uu___3))))
                        uu___1)))) uu___
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
                (let uu___ =
                   let uu___1 =
                     let uu___2 =
                       let uu___3 =
                         Pulse_Syntax_Printer.term_to_string
                           (FStar_Pervasives_Native.snd b) in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Match.fst"
                                  (Prims.of_int (212)) (Prims.of_int (35))
                                  (Prims.of_int (212)) (Prims.of_int (78)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Prims.fst"
                                  (Prims.of_int (611)) (Prims.of_int (19))
                                  (Prims.of_int (611)) (Prims.of_int (31)))))
                         (Obj.magic uu___3)
                         (fun uu___4 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___5 -> Prims.strcat uu___4 " ")) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                                (Prims.of_int (212)) (Prims.of_int (35))
                                (Prims.of_int (212)) (Prims.of_int (84)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (611)) (Prims.of_int (19))
                                (Prims.of_int (611)) (Prims.of_int (31)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> Prims.strcat ":" uu___3)) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                              (Prims.of_int (212)) (Prims.of_int (29))
                              (Prims.of_int (212)) (Prims.of_int (84)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 ->
                             Prims.strcat
                               (Prims.string_of_int
                                  (FStar_Pervasives_Native.fst b)) uu___2)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (212)) (Prims.of_int (4))
                            (Prims.of_int (212)) (Prims.of_int (85)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (212)) (Prims.of_int (4))
                            (Prims.of_int (212)) (Prims.of_int (109)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun uu___1 ->
                         let uu___2 = bindings_to_string bs1 in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Match.fst"
                                       (Prims.of_int (212))
                                       (Prims.of_int (88))
                                       (Prims.of_int (212))
                                       (Prims.of_int (109)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Prims.fst"
                                       (Prims.of_int (611))
                                       (Prims.of_int (19))
                                       (Prims.of_int (611))
                                       (Prims.of_int (31)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___4 -> Prims.strcat uu___1 uu___3))))
                        uu___1)))) uu___
let (check_branch :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Checker_Base.check_t ->
            Pulse_Syntax_Base.universe ->
              Pulse_Syntax_Base.typ ->
                Pulse_Syntax_Base.term ->
                  FStarC_Reflection_V2_Data.pattern ->
                    Pulse_Syntax_Base.st_term ->
                      FStarC_Reflection_V2_Data.binding Prims.list ->
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
                        let uu___ =
                          match readback_pat p0 with
                          | FStar_Pervasives_Native.Some p ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 -> p)))
                          | FStar_Pervasives_Native.None ->
                              Obj.magic
                                (Obj.repr
                                   (Pulse_Typing_Env.fail g
                                      (FStar_Pervasives_Native.Some
                                         (e.Pulse_Syntax_Base.range1))
                                      "readback_pat failed")) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Match.fst"
                                   (Prims.of_int (233)) (Prims.of_int (10))
                                   (Prims.of_int (234)) (Prims.of_int (48)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Match.fst"
                                   (Prims.of_int (236)) (Prims.of_int (27))
                                   (Prims.of_int (275)) (Prims.of_int (58)))))
                          (Obj.magic uu___)
                          (fun uu___1 ->
                             (fun p ->
                                let uu___1 =
                                  Obj.magic
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          FStar_List_Tot_Base.map
                                            Pulse_Typing.readback_binding bs)) in
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Match.fst"
                                              (Prims.of_int (237))
                                              (Prims.of_int (17))
                                              (Prims.of_int (237))
                                              (Prims.of_int (42)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Match.fst"
                                              (Prims.of_int (239))
                                              (Prims.of_int (54))
                                              (Prims.of_int (275))
                                              (Prims.of_int (58)))))
                                     (Obj.magic uu___1)
                                     (fun uu___2 ->
                                        (fun pulse_bs ->
                                           let uu___2 =
                                             Obj.magic
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___3 ->
                                                     Pulse_Typing.push_bindings
                                                       g pulse_bs)) in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Match.fst"
                                                         (Prims.of_int (240))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (240))
                                                         (Prims.of_int (35)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Match.fst"
                                                         (Prims.of_int (240))
                                                         (Prims.of_int (38))
                                                         (Prims.of_int (275))
                                                         (Prims.of_int (58)))))
                                                (Obj.magic uu___2)
                                                (fun uu___3 ->
                                                   (fun g' ->
                                                      let uu___3 =
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___4 ->
                                                                Pulse_Typing_Env.fresh
                                                                  g')) in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (24)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                           (Obj.magic uu___3)
                                                           (fun uu___4 ->
                                                              (fun hyp_var ->
                                                                 let uu___4 =
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Reflection_Typing.elaborate_pat
                                                                    p0 bs)) in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___4)
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    elab_p ->
                                                                    let uu___5
                                                                    =
                                                                    if
                                                                    Prims.op_Negation
                                                                    (FStar_Pervasives_Native.uu___is_Some
                                                                    elab_p)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e.Pulse_Syntax_Base.range1))
                                                                    "Failed to elab pattern into term"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    let uu___7
                                                                    =
                                                                    if
                                                                    FStarC_Reflection_V2_Data.uu___is_Tv_Unknown
                                                                    (FStarC_Reflection_V2_Builtins.inspect_ln
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    elab_p)))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e.Pulse_Syntax_Base.range1))
                                                                    "should not happen: pattern elaborated to Tv_Unknown"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    elab_p))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    elab_p_tm
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing.mk_sq_eq2
                                                                    sc_u
                                                                    sc_ty sc
                                                                    elab_p_tm)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    eq_typ ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
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
                                                                    } eq_typ)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (106)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun g'1
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    open_st_term_bs
                                                                    e
                                                                    pulse_bs)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun e1
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    {
                                                                    Pulse_Syntax_Base.hint_type
                                                                    =
                                                                    (Pulse_Syntax_Base.RENAME
                                                                    {
                                                                    Pulse_Syntax_Base.pairs
                                                                    =
                                                                    [
                                                                    (sc,
                                                                    elab_p_tm)];
                                                                    Pulse_Syntax_Base.goal
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.tac_opt
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Reflection_Util.match_rewrite_tac_tm)
                                                                    });
                                                                    Pulse_Syntax_Base.binders
                                                                    = [];
                                                                    Pulse_Syntax_Base.t
                                                                    = e1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (e1.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (e1.Pulse_Syntax_Base.effect_tag);
                                                                    Pulse_Syntax_Base.source
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    false)
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun e2
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    pre_typing2
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_br")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    ppname ->
                                                                    let uu___18
                                                                    =
                                                                    check g'1
                                                                    pre ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    ppname e2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g'1 pre
                                                                    post_hint
                                                                    r ppname))
                                                                    uu___19)))
                                                                    uu___18) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e3, c,
                                                                    e_d) ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (p,
                                                                    (Pulse_Syntax_Naming.close_st_term_n
                                                                    e3
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.fst
                                                                    pulse_bs)),
                                                                    c,
                                                                    (Pulse_Typing.TBR
                                                                    (g, sc_u,
                                                                    sc_ty,
                                                                    sc, c, p,
                                                                    e3, bs,
                                                                    (), (),
                                                                    (),
                                                                    hyp_var,
                                                                    e_d)))))))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                uu___4)))
                                                     uu___3))) uu___2)))
                               uu___1)
type ('g, 'pre, 'postuhint, 'scuu, 'scuty, 'sc) check_branches_aux_t =
  (Pulse_Syntax_Base.branch, Pulse_Syntax_Base.comp_st,
    (unit, unit, unit, unit, unit, unit, unit) Pulse_Typing.br_typing)
    FStar_Pervasives.dtuple3
let (check_branches_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Checker_Base.check_t ->
            Pulse_Syntax_Base.universe ->
              Pulse_Syntax_Base.typ ->
                Pulse_Syntax_Base.term ->
                  Pulse_Syntax_Base.branch Prims.list ->
                    (FStarC_Reflection_V2_Data.pattern *
                      FStarC_Reflection_V2_Data.binding Prims.list)
                      Prims.list ->
                      ((unit, unit, unit, unit, unit, unit)
                         check_branches_aux_t Prims.list,
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
                      let uu___ =
                        if FStar_List_Tot_Base.isEmpty brs0
                        then
                          Obj.magic
                            (Obj.repr
                               (Pulse_Typing_Env.fail g
                                  FStar_Pervasives_Native.None "empty match"))
                        else
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 -> ()))) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                                 (Prims.of_int (304)) (Prims.of_int (2))
                                 (Prims.of_int (304)) (Prims.of_int (50)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                                 (Prims.of_int (304)) (Prims.of_int (51))
                                 (Prims.of_int (314)) (Prims.of_int (3)))))
                        (Obj.magic uu___)
                        (fun uu___1 ->
                           (fun uu___1 ->
                              let uu___2 =
                                Obj.magic
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 ->
                                        fun b ->
                                          fun pbs ->
                                            let uu___4 =
                                              Obj.magic
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___5 -> b)) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Match.fst"
                                                       (Prims.of_int (307))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (307))
                                                       (Prims.of_int (20)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Match.fst"
                                                       (Prims.of_int (307))
                                                       (Prims.of_int (5))
                                                       (Prims.of_int (310))
                                                       (Prims.of_int (23)))))
                                              (Obj.magic uu___4)
                                              (fun uu___5 ->
                                                 (fun uu___5 ->
                                                    match uu___5 with
                                                    | (uu___6, e) ->
                                                        let uu___7 =
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___8 ->
                                                                  pbs)) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (23)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (23)))))
                                                             (Obj.magic
                                                                uu___7)
                                                             (fun uu___8 ->
                                                                (fun uu___8
                                                                   ->
                                                                   match uu___8
                                                                   with
                                                                   | 
                                                                   (p, bs) ->
                                                                    let uu___9
                                                                    =
                                                                    check_branch
                                                                    g pre ()
                                                                    post_hint
                                                                    check
                                                                    sc_u
                                                                    sc_ty sc
                                                                    p e bs in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (p1, e1,
                                                                    c, d) ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((p1, e1),
                                                                    c, d)))))
                                                                  uu___8)))
                                                   uu___5))) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Match.fst"
                                            (Prims.of_int (307))
                                            (Prims.of_int (5))
                                            (Prims.of_int (310))
                                            (Prims.of_int (23)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Match.fst"
                                            (Prims.of_int (311))
                                            (Prims.of_int (4))
                                            (Prims.of_int (314))
                                            (Prims.of_int (3)))))
                                   (Obj.magic uu___2)
                                   (fun uu___3 ->
                                      (fun tr1 ->
                                         let uu___3 =
                                           Pulse_Common.zipWith tr1 brs0 bnds in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Match.fst"
                                                       (Prims.of_int (312))
                                                       (Prims.of_int (10))
                                                       (Prims.of_int (312))
                                                       (Prims.of_int (31)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Match.fst"
                                                       (Prims.of_int (312))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (312))
                                                       (Prims.of_int (7)))))
                                              (Obj.magic uu___3)
                                              (fun r ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___4 -> r))))
                                        uu___3))) uu___1)
let (comp_observability :
  Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.observability) =
  fun c ->
    let uu___ = c in
    match uu___ with
    | Pulse_Syntax_Base.C_STAtomic (uu___1, obs, uu___2) -> obs
let (ctag_of_br :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit, unit, unit) check_branches_aux_t ->
                Pulse_Syntax_Base.ctag)
  =
  fun g ->
    fun pre ->
      fun post_hint ->
        fun sc_u ->
          fun sc_ty ->
            fun sc ->
              fun l ->
                let uu___ = l in
                match uu___ with
                | FStar_Pervasives.Mkdtuple3 (uu___1, c, uu___2) ->
                    Pulse_Syntax_Base.ctag_of_comp_st c
let (weaken_branch_observability :
  Pulse_Syntax_Base.observability ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.slprop ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Syntax_Base.universe ->
            Pulse_Syntax_Base.typ ->
              Pulse_Syntax_Base.term ->
                Pulse_Syntax_Base.comp_st ->
                  (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                    ->
                    ((Pulse_Syntax_Base.branch,
                       (unit, unit, unit, unit, unit, unit, unit)
                         Pulse_Typing.br_typing)
                       Prims.dtuple2,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun obs ->
    fun g ->
      fun pre ->
        fun post_hint ->
          fun sc_u ->
            fun sc_ty ->
              fun sc ->
                fun c ->
                  fun checked_br ->
                    let uu___ =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> checked_br)) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                               (Prims.of_int (337)) (Prims.of_int (29))
                               (Prims.of_int (337)) (Prims.of_int (39)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                               (Prims.of_int (337)) Prims.int_one
                               (Prims.of_int (347)) (Prims.of_int (5)))))
                      (Obj.magic uu___)
                      (fun uu___1 ->
                         match uu___1 with
                         | FStar_Pervasives.Mkdtuple3 (br, c0, typing) ->
                             (match c0 with
                              | Pulse_Syntax_Base.C_STAtomic (i, obs', st) ->
                                  if
                                    Prims.op_Negation
                                      (Pulse_Typing.sub_observability obs'
                                         obs)
                                  then
                                    FStar_Tactics_V2_Derived.fail
                                      "Cannot weaken observability"
                                  else
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 ->
                                         match typing with
                                         | Pulse_Typing.TBR
                                             (g1, sc_u1, sc_ty1, sc1, c1, p,
                                              e, bs, p1, p2, p3, hyp,
                                              st_typing)
                                             ->
                                             Prims.Mkdtuple2
                                               (br,
                                                 (Pulse_Typing.TBR
                                                    (g1, sc_u1, sc_ty1, sc1,
                                                      (Pulse_Syntax_Base.C_STAtomic
                                                         ((Pulse_Syntax_Base.comp_inames
                                                             c1), obs,
                                                           (Pulse_Syntax_Base.st_comp_of_comp
                                                              c1))), p, e,
                                                      bs, (), (), (), hyp,
                                                      (Pulse_Typing.T_Lift
                                                         ((Pulse_Typing_Env.push_binding
                                                             (Pulse_Typing.push_bindings
                                                                g1
                                                                (FStar_List_Tot_Base.map
                                                                   Pulse_Typing.readback_binding
                                                                   bs)) hyp
                                                             {
                                                               Pulse_Syntax_Base.name
                                                                 =
                                                                 (FStar_Sealed.seal
                                                                    "branch equality");
                                                               Pulse_Syntax_Base.range
                                                                 =
                                                                 FStar_Range.range_0
                                                             }
                                                             (Pulse_Typing.mk_sq_eq2
                                                                sc_u1 sc_ty1
                                                                sc1
                                                                (Pulse_Syntax_Pure.wr
                                                                   (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    (FStar_Reflection_Typing.elaborate_pat
                                                                    (Pulse_Elaborate_Pure.elab_pat
                                                                    p) bs)))
                                                                   FStar_Range.range_0))),
                                                           e, c1,
                                                           (Pulse_Syntax_Base.C_STAtomic
                                                              ((Pulse_Syntax_Base.comp_inames
                                                                  c1), obs,
                                                                (Pulse_Syntax_Base.st_comp_of_comp
                                                                   c1))),
                                                           st_typing,
                                                           (Pulse_Typing.Lift_Observability
                                                              ((Pulse_Typing_Env.push_binding
                                                                  (Pulse_Typing.push_bindings
                                                                    g1
                                                                    (FStar_List_Tot_Base.map
                                                                    Pulse_Typing.readback_binding
                                                                    bs)) hyp
                                                                  {
                                                                    Pulse_Syntax_Base.name
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "branch equality");
                                                                    Pulse_Syntax_Base.range
                                                                    =
                                                                    FStar_Range.range_0
                                                                  }
                                                                  (Pulse_Typing.mk_sq_eq2
                                                                    sc_u1
                                                                    sc_ty1
                                                                    sc1
                                                                    (Pulse_Syntax_Pure.wr
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    (FStar_Reflection_Typing.elaborate_pat
                                                                    (Pulse_Elaborate_Pure.elab_pat
                                                                    p) bs)))
                                                                    FStar_Range.range_0))),
                                                                c1, obs))))))))))
let rec (max_obs :
  Pulse_Syntax_Base.comp_st Prims.list ->
    Pulse_Syntax_Base.observability -> Pulse_Syntax_Base.observability)
  =
  fun checked_brs ->
    fun obs ->
      match checked_brs with
      | [] -> obs
      | c'::rest ->
          (match c' with
           | Pulse_Syntax_Base.C_ST uu___ -> max_obs rest obs
           | Pulse_Syntax_Base.C_STGhost (uu___, uu___1) -> max_obs rest obs
           | Pulse_Syntax_Base.C_STAtomic (uu___, obs', uu___1) ->
               max_obs rest (Pulse_Typing.join_obs obs obs'))
let (join_branches :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.ctag ->
                (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                  Prims.list ->
                  ((Pulse_Syntax_Base.comp_st,
                     (Pulse_Syntax_Base.branch,
                       (unit, unit, unit, unit, unit, unit, unit)
                         Pulse_Typing.br_typing)
                       Prims.dtuple2 Prims.list)
                     Prims.dtuple2,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun g ->
                     fun pre ->
                       fun post_hint ->
                         fun sc_u ->
                           fun sc_ty ->
                             fun sc ->
                               fun ct ->
                                 fun checked_brs ->
                                   match checked_brs with
                                   | [] ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_V2_Derived.fail
                                               "Impossible: empty match"))
                                   | checked_br::rest ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___ =
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 -> checked_br)) in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Match.fst"
                                                        (Prims.of_int (372))
                                                        (Prims.of_int (25))
                                                        (Prims.of_int (372))
                                                        (Prims.of_int (35)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Match.fst"
                                                        (Prims.of_int (371))
                                                        (Prims.of_int (23))
                                                        (Prims.of_int (388))
                                                        (Prims.of_int (26)))))
                                               (Obj.magic uu___)
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     match uu___1 with
                                                     | FStar_Pervasives.Mkdtuple3
                                                         (br, c, d) ->
                                                         (match c with
                                                          | Pulse_Syntax_Base.C_ST
                                                              uu___2 ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    ((Prims.Mkdtuple2
                                                                    (br, d))
                                                                    ::
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c',
                                                                    d1) ->
                                                                    Prims.Mkdtuple2
                                                                    (br1, d1))
                                                                    rest))))))
                                                          | Pulse_Syntax_Base.C_STGhost
                                                              (uu___2,
                                                               uu___3)
                                                              ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    ((Prims.Mkdtuple2
                                                                    (br, d))
                                                                    ::
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c',
                                                                    d1) ->
                                                                    Prims.Mkdtuple2
                                                                    (br1, d1))
                                                                    rest))))))
                                                          | Pulse_Syntax_Base.C_STAtomic
                                                              (i, obs, stc)
                                                              ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (let uu___2
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    max_obs
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives.__proj__Mkdtuple3__item___2
                                                                    rest) obs)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___2)
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    max_obs1
                                                                    ->
                                                                    let uu___3
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (i,
                                                                    max_obs1,
                                                                    stc))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___3)
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun c1
                                                                    ->
                                                                    let uu___4
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    (weaken_branch_observability
                                                                    max_obs1
                                                                    g pre
                                                                    post_hint
                                                                    sc_u
                                                                    sc_ty sc
                                                                    c1)
                                                                    checked_brs in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___4)
                                                                    (fun
                                                                    checked_brs1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.Mkdtuple2
                                                                    (c1,
                                                                    checked_brs1)))))
                                                                    uu___4)))
                                                                    uu___3)))))
                                                    uu___1)))) uu___7 uu___6
                    uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let rec (least_tag :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                Prims.list -> Pulse_Syntax_Base.ctag)
  =
  fun g ->
    fun pre ->
      fun post_hint ->
        fun sc_u ->
          fun sc_ty ->
            fun sc ->
              fun checked_brs ->
                match checked_brs with
                | [] -> Pulse_Syntax_Base.STT_Ghost
                | checked_br::rest ->
                    let uu___ = checked_br in
                    (match uu___ with
                     | FStar_Pervasives.Mkdtuple3 (uu___1, c, uu___2) ->
                         (match c with
                          | Pulse_Syntax_Base.C_ST uu___3 ->
                              Pulse_Syntax_Base.STT
                          | Pulse_Syntax_Base.C_STGhost (uu___3, uu___4) ->
                              least_tag g pre post_hint sc_u sc_ty sc rest
                          | Pulse_Syntax_Base.C_STAtomic (i, uu___3, uu___4)
                              -> Pulse_Syntax_Base.STT_Atomic))
let (weaken_branch_tag_to :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.ctag ->
                (unit, unit, unit, unit, unit, unit) check_branches_aux_t ->
                  ((unit, unit, unit, unit, unit, unit) check_branches_aux_t,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun post_hint ->
        fun sc_u ->
          fun sc_ty ->
            fun sc ->
              fun ct ->
                fun br ->
                  let uu___ =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> br)) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                             (Prims.of_int (407)) (Prims.of_int (22))
                             (Prims.of_int (407)) (Prims.of_int (24)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                             (Prims.of_int (407)) Prims.int_one
                             (Prims.of_int (426)) (Prims.of_int (5)))))
                    (Obj.magic uu___)
                    (fun uu___1 ->
                       (fun uu___1 ->
                          match uu___1 with
                          | FStar_Pervasives.Mkdtuple3 (pe, c, d) ->
                              if (Pulse_Syntax_Base.ctag_of_comp_st c) = ct
                              then
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 -> br)))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (let uu___3 =
                                        Obj.magic
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___4 ->
                                                (FStar_Pervasives_Native.snd
                                                   pe).Pulse_Syntax_Base.range1)) in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Match.fst"
                                                 (Prims.of_int (410))
                                                 (Prims.of_int (12))
                                                 (Prims.of_int (410))
                                                 (Prims.of_int (26)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Match.fst"
                                                 (Prims.of_int (411))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (426))
                                                 (Prims.of_int (5)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           (fun r ->
                                              match (ct, c) with
                                              | (Pulse_Syntax_Base.STT_Ghost,
                                                 Pulse_Syntax_Base.C_STAtomic
                                                 (uu___4, uu___5, uu___6)) ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_V2_Derived.fail
                                                          "Unexpected least effect"))
                                              | (Pulse_Syntax_Base.STT_Ghost,
                                                 Pulse_Syntax_Base.C_ST
                                                 uu___4) ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_V2_Derived.fail
                                                          "Unexpected least effect"))
                                              | (Pulse_Syntax_Base.STT_Atomic,
                                                 Pulse_Syntax_Base.C_ST
                                                 uu___4) ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (Pulse_Typing_Env.fail
                                                          g
                                                          (FStar_Pervasives_Native.Some
                                                             r)
                                                          "Cannot lift a computation from ST to atomic"))
                                              | (Pulse_Syntax_Base.STT,
                                                 uu___4) ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (Pulse_Typing_Env.fail
                                                          g
                                                          (FStar_Pervasives_Native.Some
                                                             r)
                                                          "Cannot lift a branch to ST"))
                                              | (Pulse_Syntax_Base.STT_Atomic,
                                                 Pulse_Syntax_Base.C_STGhost
                                                 (uu___4, uu___5)) ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (let uu___6 =
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___7 ->
                                                                  d)) in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Match.fst"
                                                                   (Prims.of_int (422))
                                                                   (Prims.of_int (57))
                                                                   (Prims.of_int (422))
                                                                   (Prims.of_int (58)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Match.fst"
                                                                   (Prims.of_int (421))
                                                                   (Prims.of_int (35))
                                                                   (Prims.of_int (426))
                                                                   (Prims.of_int (5)))))
                                                          (Obj.magic uu___6)
                                                          (fun uu___7 ->
                                                             (fun uu___7 ->
                                                                match uu___7
                                                                with
                                                                | Pulse_Typing.TBR
                                                                    (g1,
                                                                    sc_u1,
                                                                    sc_ty1,
                                                                    sc1, c1,
                                                                    p, e, bs,
                                                                    pf1, pf2,
                                                                    pf3, h,
                                                                    d1) ->
                                                                    let uu___8
                                                                    =
                                                                    Pulse_Typing_Combinators.lift_ghost_atomic
                                                                    (Pulse_Typing_Env.push_binding
                                                                    (Pulse_Typing.push_bindings
                                                                    g1
                                                                    (FStar_List_Tot_Base.map
                                                                    Pulse_Typing.readback_binding
                                                                    bs)) h
                                                                    {
                                                                    Pulse_Syntax_Base.name
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "branch equality");
                                                                    Pulse_Syntax_Base.range
                                                                    =
                                                                    FStar_Range.range_0
                                                                    }
                                                                    (Pulse_Typing.mk_sq_eq2
                                                                    sc_u1
                                                                    sc_ty1
                                                                    sc1
                                                                    (Pulse_Syntax_Pure.wr
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    (FStar_Reflection_Typing.elaborate_pat
                                                                    (Pulse_Elaborate_Pure.elab_pat
                                                                    p) bs)))
                                                                    FStar_Range.range_0)))
                                                                    e c1 d1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun d2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (pe,
                                                                    (Pulse_Typing_Combinators.st_ghost_as_atomic
                                                                    c1),
                                                                    (Pulse_Typing.TBR
                                                                    (g1,
                                                                    sc_u1,
                                                                    sc_ty1,
                                                                    sc1,
                                                                    (Pulse_Typing_Combinators.st_ghost_as_atomic
                                                                    c1), p,
                                                                    e, bs,
                                                                    (), (),
                                                                    (), h,
                                                                    d2)))))))
                                                               uu___7))))
                                             uu___4)))) uu___1)
let (weaken_branch_tags :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                Prims.list ->
                ((Pulse_Syntax_Base.ctag,
                   (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                     Prims.list)
                   Prims.dtuple2,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun post_hint ->
        fun sc_u ->
          fun sc_ty ->
            fun sc ->
              fun checked_brs ->
                let uu___ =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          least_tag g pre post_hint sc_u sc_ty sc checked_brs)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                           (Prims.of_int (433)) (Prims.of_int (11))
                           (Prims.of_int (433)) (Prims.of_int (32)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                           (Prims.of_int (433)) (Prims.of_int (35))
                           (Prims.of_int (435)) (Prims.of_int (15)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun ct ->
                        let uu___1 =
                          FStar_Tactics_Util.map
                            (weaken_branch_tag_to g pre post_hint sc_u sc_ty
                               sc ct) checked_brs in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Match.fst"
                                      (Prims.of_int (434))
                                      (Prims.of_int (12))
                                      (Prims.of_int (434))
                                      (Prims.of_int (55)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Match.fst"
                                      (Prims.of_int (435)) (Prims.of_int (2))
                                      (Prims.of_int (435))
                                      (Prims.of_int (15)))))
                             (Obj.magic uu___1)
                             (fun brs ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 -> Prims.Mkdtuple2 (ct, brs)))))
                       uu___1)
let (maybe_weaken_branch_tags :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                Prims.list ->
                ((Pulse_Syntax_Base.ctag,
                   (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                     Prims.list)
                   Prims.dtuple2,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun g ->
                   fun pre ->
                     fun post_hint ->
                       fun sc_u ->
                         fun sc_ty ->
                           fun sc ->
                             fun checked_brs ->
                               match post_hint.Pulse_Typing.effect_annot with
                               | Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                   uu___ ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___1 =
                                           Obj.magic
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   least_tag g pre post_hint
                                                     sc_u sc_ty sc
                                                     checked_brs)) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Match.fst"
                                                    (Prims.of_int (443))
                                                    (Prims.of_int (13))
                                                    (Prims.of_int (443))
                                                    (Prims.of_int (34)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Match.fst"
                                                    (Prims.of_int (443))
                                                    (Prims.of_int (37))
                                                    (Prims.of_int (445))
                                                    (Prims.of_int (17)))))
                                           (Obj.magic uu___1)
                                           (fun uu___2 ->
                                              (fun ct ->
                                                 let uu___2 =
                                                   FStar_Tactics_Util.map
                                                     (weaken_branch_tag_to g
                                                        pre post_hint sc_u
                                                        sc_ty sc ct)
                                                     checked_brs in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Match.fst"
                                                               (Prims.of_int (444))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (444))
                                                               (Prims.of_int (57)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Match.fst"
                                                               (Prims.of_int (445))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (445))
                                                               (Prims.of_int (17)))))
                                                      (Obj.magic uu___2)
                                                      (fun brs ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 ->
                                                              Prims.Mkdtuple2
                                                                (ct, brs)))))
                                                uu___2)))
                               | uu___ ->
                                   Obj.magic
                                     (Obj.repr
                                        (match checked_brs with
                                         | [] ->
                                             Obj.repr
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___1 ->
                                                     Prims.Mkdtuple2
                                                       (Pulse_Syntax_Base.STT_Ghost,
                                                         [])))
                                         | hd::tl ->
                                             Obj.repr
                                               (let uu___1 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          ctag_of_br g pre
                                                            post_hint sc_u
                                                            sc_ty sc hd)) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Match.fst"
                                                           (Prims.of_int (450))
                                                           (Prims.of_int (15))
                                                           (Prims.of_int (450))
                                                           (Prims.of_int (28)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Match.fst"
                                                           (Prims.of_int (450))
                                                           (Prims.of_int (31))
                                                           (Prims.of_int (452))
                                                           (Prims.of_int (27)))))
                                                  (Obj.magic uu___1)
                                                  (fun uu___2 ->
                                                     (fun ct ->
                                                        let uu___2 =
                                                          FStar_Tactics_Util.map
                                                            (fun uu___3 ->
                                                               (fun x ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    x)))
                                                                 uu___3)
                                                            checked_brs in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (139)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (27)))))
                                                             (Obj.magic
                                                                uu___2)
                                                             (fun
                                                                checked_brs1
                                                                ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___3
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (ct,
                                                                    checked_brs1)))))
                                                       uu___2))))) uu___6
                  uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (check_branches :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Checker_Base.check_t ->
            Pulse_Syntax_Base.universe ->
              Pulse_Syntax_Base.typ ->
                Pulse_Syntax_Base.term ->
                  Pulse_Syntax_Base.branch Prims.list ->
                    (FStarC_Reflection_V2_Data.pattern *
                      FStarC_Reflection_V2_Data.binding Prims.list)
                      Prims.list ->
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
                      let uu___ =
                        check_branches_aux g pre () post_hint check sc_u
                          sc_ty sc brs0 bnds in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                                 (Prims.of_int (468)) (Prims.of_int (20))
                                 (Prims.of_int (468)) (Prims.of_int (95)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                                 (Prims.of_int (468)) (Prims.of_int (98))
                                 (Prims.of_int (482)) (Prims.of_int (18)))))
                        (Obj.magic uu___)
                        (fun uu___1 ->
                           (fun checked_brs ->
                              let uu___1 =
                                maybe_weaken_branch_tags g pre post_hint sc_u
                                  sc_ty sc checked_brs in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Match.fst"
                                            (Prims.of_int (469))
                                            (Prims.of_int (30))
                                            (Prims.of_int (469))
                                            (Prims.of_int (66)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Match.fst"
                                            (Prims.of_int (468))
                                            (Prims.of_int (98))
                                            (Prims.of_int (482))
                                            (Prims.of_int (18)))))
                                   (Obj.magic uu___1)
                                   (fun uu___2 ->
                                      (fun uu___2 ->
                                         match uu___2 with
                                         | Prims.Mkdtuple2 (ct, checked_brs1)
                                             ->
                                             let uu___3 =
                                               join_branches g pre post_hint
                                                 sc_u sc_ty sc ct
                                                 checked_brs1 in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Match.fst"
                                                           (Prims.of_int (470))
                                                           (Prims.of_int (30))
                                                           (Prims.of_int (470))
                                                           (Prims.of_int (58)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Match.fst"
                                                           (Prims.of_int (469))
                                                           (Prims.of_int (69))
                                                           (Prims.of_int (482))
                                                           (Prims.of_int (18)))))
                                                  (Obj.magic uu___3)
                                                  (fun uu___4 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___5 ->
                                                          match uu___4 with
                                                          | Prims.Mkdtuple2
                                                              (c0,
                                                               checked_brs2)
                                                              ->
                                                              FStar_Pervasives.Mkdtuple3
                                                                ((FStar_List_Tot_Base.map
                                                                    FStar_Pervasives.dfst
                                                                    checked_brs2),
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
                                                                    d))::rest
                                                                    ->
                                                                    Pulse_Typing.TBRS_1
                                                                    (c0, p,
                                                                    e, d,
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives.dfst
                                                                    rest),
                                                                    (aux rest)) in
                                                                   aux
                                                                    checked_brs2))))))
                                        uu___2))) uu___1)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.branch Prims.list ->
                Pulse_Checker_Base.check_t ->
                  ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun sc ->
              fun brs ->
                fun check1 ->
                  let uu___ =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            Pulse_Typing_Env.push_context_no_range g
                              "check_match")) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                             (Prims.of_int (496)) (Prims.of_int (10))
                             (Prims.of_int (496)) (Prims.of_int (64)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                             (Prims.of_int (496)) (Prims.of_int (67))
                             (Prims.of_int (545)) (Prims.of_int (55)))))
                    (Obj.magic uu___)
                    (fun uu___1 ->
                       (fun g1 ->
                          let uu___1 =
                            Obj.magic
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 ->
                                    Pulse_RuntimeUtils.range_of_term sc)) in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Match.fst"
                                        (Prims.of_int (498))
                                        (Prims.of_int (17))
                                        (Prims.of_int (498))
                                        (Prims.of_int (52)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Match.fst"
                                        (Prims.of_int (498))
                                        (Prims.of_int (55))
                                        (Prims.of_int (545))
                                        (Prims.of_int (55)))))
                               (Obj.magic uu___1)
                               (fun uu___2 ->
                                  (fun sc_range ->
                                     let uu___2 =
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___3 -> brs)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Match.fst"
                                                   (Prims.of_int (499))
                                                   (Prims.of_int (17))
                                                   (Prims.of_int (499))
                                                   (Prims.of_int (20)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Match.fst"
                                                   (Prims.of_int (499))
                                                   (Prims.of_int (23))
                                                   (Prims.of_int (545))
                                                   (Prims.of_int (55)))))
                                          (Obj.magic uu___2)
                                          (fun uu___3 ->
                                             (fun orig_brs ->
                                                let uu___3 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___4 ->
                                                          FStar_List_Tot_Base.length
                                                            brs)) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Match.fst"
                                                              (Prims.of_int (500))
                                                              (Prims.of_int (12))
                                                              (Prims.of_int (500))
                                                              (Prims.of_int (24)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Match.fst"
                                                              (Prims.of_int (500))
                                                              (Prims.of_int (27))
                                                              (Prims.of_int (545))
                                                              (Prims.of_int (55)))))
                                                     (Obj.magic uu___3)
                                                     (fun uu___4 ->
                                                        (fun nbr ->
                                                           let uu___4 =
                                                             Pulse_Checker_Pure.compute_tot_term_type_and_u
                                                               g1 sc in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (87)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (55)))))
                                                                (Obj.magic
                                                                   uu___4)
                                                                (fun uu___5
                                                                   ->
                                                                   (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (sc1,
                                                                    sc_u,
                                                                    sc_ty,
                                                                    sc_ty_typing,
                                                                    sc_typing)
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_List_Tot_Base.map
                                                                    Pulse_Elaborate_Pure.elab_pat
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.fst
                                                                    brs))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (508))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    elab_pats
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.check_match_complete
                                                                    (Pulse_Typing.elab_env
                                                                    g1) sc1
                                                                    sc_ty
                                                                    elab_pats in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (518))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
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
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (elab_pats',
                                                                    bnds,
                                                                    (Pulse_Typing.PC_Elab
                                                                    (g1, sc1,
                                                                    sc_ty,
                                                                    elab_pats',
                                                                    bnds,
                                                                    (FStar_Reflection_Typing.MC_Tok
                                                                    ((Pulse_Typing.elab_env
                                                                    g1), sc1,
                                                                    sc_ty,
                                                                    elab_pats',
                                                                    bnds, ())))))))))
                                                                    uu___9) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (518))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (508))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (elab_pats',
                                                                    bnds',
                                                                    complete_d)
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> uu___8)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Common.map_opt
                                                                    readback_pat
                                                                    elab_pats')) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    new_pats
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    new_pats
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    sc_range)
                                                                    "failed to readback new patterns"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Pulse_Common.zipWith
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    fun
                                                                    uu___15
                                                                    ->
                                                                    (fun p ->
                                                                    fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    (uu___17,
                                                                    e) ->
                                                                    (p, e))))
                                                                    uu___16
                                                                    uu___15)
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    new_pats)
                                                                    brs in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun brs1
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    check_branches
                                                                    g1 pre ()
                                                                    post_hint
                                                                    check1
                                                                    sc_u
                                                                    sc_ty sc1
                                                                    brs1
                                                                    (Pulse_Common.zip
                                                                    elab_pats'
                                                                    bnds') in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (brs2, c,
                                                                    brs_d) ->
                                                                    let uu___17
                                                                    =
                                                                    Pulse_Checker_Base.comp_typing_from_post_hint
                                                                    g c ()
                                                                    post_hint in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Pulse_Typing.T_Match
                                                                    (g1,
                                                                    sc_u,
                                                                    sc_ty,
                                                                    sc1, (),
                                                                    (), c,
                                                                    (), brs2,
                                                                    brs_d,
                                                                    complete_d))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wrst
                                                                    c
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
                                                                    d))
                                                                    res_ppname))
                                                                    uu___19)))
                                                                    uu___18)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___5)))
                                                          uu___4))) uu___3)))
                                    uu___2))) uu___1)