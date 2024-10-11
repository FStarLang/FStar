open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (k_intro_pure :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit ->
          Pulse_Syntax_Base.slprop ->
            ((unit, unit, unit, unit)
               Pulse_Checker_Base.continuation_elaborator,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      fun d ->
        fun token ->
          fun frame ->
            let uu___ =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      Pulse_Typing.wtag
                        (FStar_Pervasives_Native.Some
                           Pulse_Syntax_Base.STT_Ghost)
                        (Pulse_Syntax_Base.Tm_IntroPure
                           { Pulse_Syntax_Base.p3 = p }))) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "Pulse.Checker.Prover.IntroPure.fst"
                       (Prims.of_int (42)) (Prims.of_int (10))
                       (Prims.of_int (42)) (Prims.of_int (50)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "Pulse.Checker.Prover.IntroPure.fst"
                       (Prims.of_int (42)) (Prims.of_int (53))
                       (Prims.of_int (76)) (Prims.of_int (30)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun t ->
                    let uu___1 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___2 -> Pulse_Typing.comp_intro_pure p)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.IntroPure.fst"
                                  (Prims.of_int (43)) (Prims.of_int (10))
                                  (Prims.of_int (43)) (Prims.of_int (27)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.IntroPure.fst"
                                  (Prims.of_int (43)) (Prims.of_int (30))
                                  (Prims.of_int (76)) (Prims.of_int (30)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun c ->
                               let uu___2 =
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 ->
                                         Pulse_Typing.T_IntroPure
                                           (g, p, (), ()))) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.IntroPure.fst"
                                             (Prims.of_int (44))
                                             (Prims.of_int (28))
                                             (Prims.of_int (44))
                                             (Prims.of_int (51)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.IntroPure.fst"
                                             (Prims.of_int (44))
                                             (Prims.of_int (54))
                                             (Prims.of_int (76))
                                             (Prims.of_int (30)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun d1 ->
                                          let uu___3 =
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___4 ->
                                                    Pulse_Typing_Env.fresh g)) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.IntroPure.fst"
                                                        (Prims.of_int (46))
                                                        (Prims.of_int (10))
                                                        (Prims.of_int (46))
                                                        (Prims.of_int (17)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.IntroPure.fst"
                                                        (Prims.of_int (49))
                                                        (Prims.of_int (30))
                                                        (Prims.of_int (76))
                                                        (Prims.of_int (30)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun x ->
                                                     let uu___4 =
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___5 ->
                                                               Pulse_Syntax_Base.mk_ppname_no_range
                                                                 "_pintrop")) in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.IntroPure.fst"
                                                                   (Prims.of_int (51))
                                                                   (Prims.of_int (15))
                                                                   (Prims.of_int (51))
                                                                   (Prims.of_int (44)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.IntroPure.fst"
                                                                   (Prims.of_int (51))
                                                                   (Prims.of_int (47))
                                                                   (Prims.of_int (76))
                                                                   (Prims.of_int (30)))))
                                                          (Obj.magic uu___4)
                                                          (fun uu___5 ->
                                                             (fun ppname ->
                                                                let uu___5 =
                                                                  Pulse_Checker_Base.continuation_elaborator_with_bind
                                                                    g frame c
                                                                    t d1 ()
                                                                    (ppname,
                                                                    x) in
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun k ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun
                                                                    post_hint
                                                                    ->
                                                                    fun r ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    r)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (30)))))
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
                                                                    (t1, c1,
                                                                    d11) ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> d11)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun d12
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    empty_env
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing_Metatheory.st_typing_weakening
                                                                    g
                                                                    empty_env
                                                                    t1 c1 d12
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    Pulse_Typing.tm_unit))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun d13
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    g
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    Pulse_Typing.tm_unit)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    frame
                                                                    Pulse_Syntax_Pure.tm_emp)
                                                                    frame
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.tm_pure
                                                                    p) frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    frame
                                                                    (Pulse_Syntax_Pure.tm_pure
                                                                    p)) k ()
                                                                    ()
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (t1, c1,
                                                                    d13))))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___8)))))
                                                               uu___5)))
                                                    uu___4))) uu___3)))
                              uu___2))) uu___1)
type pure_uv_heuristic_t =
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) Prims.dtuple2
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr
let (is_eq2_uvar : pure_uv_heuristic_t) =
  fun uvs ->
    fun t ->
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              match Pulse_Syntax_Pure.is_eq2 t with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (uu___1, l, r) ->
                  (match Pulse_Syntax_Pure.is_var l with
                   | FStar_Pervasives_Native.Some nm ->
                       if
                         FStar_Set.mem nm.Pulse_Syntax_Base.nm_index
                           (Pulse_Typing_Env.dom uvs)
                       then
                         FStar_Pervasives_Native.Some
                           (Prims.Mkdtuple2
                              ((nm.Pulse_Syntax_Base.nm_index), r))
                       else FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.None ->
                       (match Pulse_Syntax_Pure.is_var r with
                        | FStar_Pervasives_Native.Some nm ->
                            if
                              FStar_Set.mem nm.Pulse_Syntax_Base.nm_index
                                (Pulse_Typing_Env.dom uvs)
                            then
                              FStar_Pervasives_Native.Some
                                (Prims.Mkdtuple2
                                   ((nm.Pulse_Syntax_Base.nm_index), l))
                            else FStar_Pervasives_Native.None
                        | uu___2 -> FStar_Pervasives_Native.None))))
let (is_host_var :
  FStarC_Reflection_Types.term ->
    Pulse_Syntax_Base.nm FStar_Pervasives_Native.option)
  =
  fun x ->
    match FStarC_Reflection_V2_Builtins.inspect_ln x with
    | FStarC_Reflection_V2_Data.Tv_Var nv ->
        let nv_view = FStarC_Reflection_V2_Builtins.inspect_namedv nv in
        FStar_Pervasives_Native.Some
          {
            Pulse_Syntax_Base.nm_index =
              (nv_view.FStarC_Reflection_V2_Data.uniq);
            Pulse_Syntax_Base.nm_ppname =
              (Pulse_Syntax_Base.mk_ppname
                 nv_view.FStarC_Reflection_V2_Data.ppname
                 (FStarC_Reflection_V2_Builtins.range_of_term x))
          }
    | uu___ -> FStar_Pervasives_Native.None
let (is_uvar_implication : pure_uv_heuristic_t) =
  fun uvs ->
    fun t ->
      let uu___ =
        Pulse_Checker_Base.debug uvs
          (fun uu___1 ->
             let uu___2 = Pulse_Syntax_Printer.term_to_string t in
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range
                        "Pulse.Checker.Prover.IntroPure.fst"
                        (Prims.of_int (127)) (Prims.of_int (69))
                        (Prims.of_int (127)) (Prims.of_int (89)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                        (Prims.of_int (19)) (Prims.of_int (611))
                        (Prims.of_int (31))))) (Obj.magic uu___2)
               (fun uu___3 ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___4 ->
                       Prims.strcat "is_uvar_implication??: "
                         (Prims.strcat uu___3 "\n")))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.IntroPure.fst"
                 (Prims.of_int (127)) (Prims.of_int (4)) (Prims.of_int (127))
                 (Prims.of_int (90)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.IntroPure.fst"
                 (Prims.of_int (128)) (Prims.of_int (4)) (Prims.of_int (169))
                 (Prims.of_int (15))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match Pulse_Syntax_Pure.inspect_term t with
              | Pulse_Syntax_Pure.Tm_FStar uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (let uu___3 =
                          Obj.magic
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 -> t)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Prover.IntroPure.fst"
                                   (Prims.of_int (130)) (Prims.of_int (15))
                                   (Prims.of_int (130)) (Prims.of_int (16)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Prover.IntroPure.fst"
                                   (Prims.of_int (130)) (Prims.of_int (19))
                                   (Prims.of_int (167)) (Prims.of_int (17)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             (fun tt ->
                                let uu___4 =
                                  FStar_Reflection_V2_Formula.term_as_formula'
                                    tt in
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Prover.IntroPure.fst"
                                              (Prims.of_int (131))
                                              (Prims.of_int (14))
                                              (Prims.of_int (131))
                                              (Prims.of_int (36)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Prover.IntroPure.fst"
                                              (Prims.of_int (132))
                                              (Prims.of_int (6))
                                              (Prims.of_int (167))
                                              (Prims.of_int (17)))))
                                     (Obj.magic uu___4)
                                     (fun uu___5 ->
                                        (fun f ->
                                           match f with
                                           | FStar_Reflection_V2_Formula.Implies
                                               (t0, t1) ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (let uu___5 =
                                                       Pulse_Checker_Base.debug
                                                         uvs
                                                         (fun uu___6 ->
                                                            let uu___7 =
                                                              FStarC_Tactics_V2_Builtins.term_to_string
                                                                t0 in
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (98)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                              (Obj.magic
                                                                 uu___7)
                                                              (fun uu___8 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "is_uvar_implication, LHS=: "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\n")))) in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.IntroPure.fst"
                                                                (Prims.of_int (134))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (134))
                                                                (Prims.of_int (99)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.IntroPure.fst"
                                                                (Prims.of_int (135))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (165))
                                                                (Prims.of_int (11)))))
                                                       (Obj.magic uu___5)
                                                       (fun uu___6 ->
                                                          (fun uu___6 ->
                                                             match FStarC_Reflection_V2_Builtins.inspect_ln
                                                                    t0
                                                             with
                                                             | FStarC_Reflection_V2_Data.Tv_Unknown
                                                                 ->
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.None)))
                                                             | uu___7 ->
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Syntax_Pure.wr
                                                                    t0
                                                                    FStar_Range.range_0)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun t01
                                                                    ->
                                                                    match 
                                                                    Pulse_Syntax_Pure.is_eq2
                                                                    t01
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (ty, lhs,
                                                                    rhs) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    Pulse_Syntax_Base.eq_tm
                                                                    ty
                                                                    (Pulse_Syntax_Pure.wr
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "bool"])))
                                                                    FStar_Range.range_0)
                                                                    then
                                                                    Obj.repr
                                                                    (let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    fun
                                                                    uu___11
                                                                    ->
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun
                                                                    maybe_var
                                                                    ->
                                                                    fun
                                                                    other_side
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match 
                                                                    Pulse_Syntax_Pure.is_var
                                                                    lhs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    nm ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    nm.Pulse_Syntax_Base.nm_index
                                                                    (Pulse_Typing_Env.dom
                                                                    uvs)
                                                                    then
                                                                    (match 
                                                                    Pulse_Syntax_Pure.inspect_term
                                                                    rhs
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Pure.Tm_FStar
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    ((nm.Pulse_Syntax_Base.nm_index),
                                                                    (Pulse_Syntax_Pure.wr
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "op_Negation"]))),
                                                                    (rhs,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))
                                                                    FStar_Range.range_0)))
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    else
                                                                    FStar_Pervasives_Native.None)))
                                                                    uu___12
                                                                    uu___11
                                                                    uu___10)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    try_negated
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    try_negated
                                                                    lhs rhs in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (try_negated
                                                                    rhs lhs))
                                                                    | 
                                                                    x ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> x))))
                                                                    uu___11)))
                                                                    uu___10))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives_Native.None)))))
                                                                    uu___9))))
                                                            uu___6)))
                                           | uu___5 ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___6 ->
                                                          FStar_Pervasives_Native.None))))
                                          uu___5))) uu___4)))
              | uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> FStar_Pervasives_Native.None))))
             uu___1)
let (pure_uvar_heursitics : pure_uv_heuristic_t) =
  let h = [is_eq2_uvar; is_uvar_implication] in
  fun uvs ->
    fun t ->
      let rec loop uu___ =
        (fun h1 ->
           match h1 with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.None)))
           | h2::hs ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = h2 uvs t in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.IntroPure.fst"
                                (Prims.of_int (179)) (Prims.of_int (16))
                                (Prims.of_int (179)) (Prims.of_int (23)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.IntroPure.fst"
                                (Prims.of_int (179)) (Prims.of_int (10))
                                (Prims.of_int (181)) (Prims.of_int (48)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | FStar_Pervasives_Native.None ->
                                 Obj.magic (Obj.repr (loop hs))
                             | FStar_Pervasives_Native.Some (Prims.Mkdtuple2
                                 (uv, e)) ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            FStar_Pervasives_Native.Some
                                              (Prims.Mkdtuple2 (uv, e))))))
                            uu___1)))) uu___ in
      loop h
let rec (try_collect_substs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Checker_Prover_Substs.ss_t, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun uvs ->
         fun t ->
           match Pulse_Syntax_Pure.inspect_term t with
           | Pulse_Syntax_Pure.Tm_FStar uu___ ->
               Obj.magic
                 (Obj.repr
                    (let uu___1 =
                       Obj.magic
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> t)) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.IntroPure.fst"
                                (Prims.of_int (189)) (Prims.of_int (13))
                                (Prims.of_int (189)) (Prims.of_int (14)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.IntroPure.fst"
                                (Prims.of_int (189)) (Prims.of_int (17))
                                (Prims.of_int (209)) (Prims.of_int (7)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun rt ->
                             let uu___2 =
                               FStar_Reflection_V2_Formula.term_as_formula'
                                 rt in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Prover.IntroPure.fst"
                                           (Prims.of_int (190))
                                           (Prims.of_int (12))
                                           (Prims.of_int (190))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Prover.IntroPure.fst"
                                           (Prims.of_int (192))
                                           (Prims.of_int (6))
                                           (Prims.of_int (208))
                                           (Prims.of_int (26)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun f ->
                                        match f with
                                        | FStar_Reflection_V2_Formula.And
                                            (rt0, rt1) ->
                                            let uu___3 =
                                              try_collect_substs uvs
                                                (Pulse_Syntax_Pure.wr rt0
                                                   FStar_Range.range_0) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.IntroPure.fst"
                                                          (Prims.of_int (194))
                                                          (Prims.of_int (18))
                                                          (Prims.of_int (194))
                                                          (Prims.of_int (69)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.IntroPure.fst"
                                                          (Prims.of_int (194))
                                                          (Prims.of_int (72))
                                                          (Prims.of_int (200))
                                                          (Prims.of_int (21)))))
                                                 (Obj.magic uu___3)
                                                 (fun uu___4 ->
                                                    (fun ss0 ->
                                                       let uu___4 =
                                                         try_collect_substs
                                                           uvs
                                                           (Pulse_Syntax_Pure.wr
                                                              rt1
                                                              FStar_Range.range_0) in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (69)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (21)))))
                                                            (Obj.magic uu___4)
                                                            (fun ss1 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___5
                                                                    ->
                                                                    if
                                                                    Pulse_Checker_Prover_Substs.check_disjoint
                                                                    ss0 ss1
                                                                    then
                                                                    Pulse_Checker_Prover_Substs.push_ss
                                                                    ss0 ss1
                                                                    else
                                                                    Pulse_Checker_Prover_Substs.empty))))
                                                      uu___4))
                                        | uu___3 ->
                                            let uu___4 =
                                              pure_uvar_heursitics uvs t in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.IntroPure.fst"
                                                          (Prims.of_int (202))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (202))
                                                          (Prims.of_int (40)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.IntroPure.fst"
                                                          (Prims.of_int (202))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (208))
                                                          (Prims.of_int (26)))))
                                                 (Obj.magic uu___4)
                                                 (fun uu___5 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___6 ->
                                                         match uu___5 with
                                                         | FStar_Pervasives_Native.Some
                                                             (Prims.Mkdtuple2
                                                             (uv, e)) ->
                                                             Pulse_Checker_Prover_Substs.push
                                                               Pulse_Checker_Prover_Substs.empty
                                                               uv e
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             Pulse_Checker_Prover_Substs.empty))))
                                       uu___3))) uu___2)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> Pulse_Checker_Prover_Substs.empty))))
        uu___1 uu___
let (intro_pure :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.slprop Prims.list ->
          unit ->
            (unit Pulse_Checker_Prover_Base.prover_state
               FStar_Pervasives_Native.option,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      fun t ->
        fun unsolved' ->
          fun uu___ ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      Pulse_Checker_Prover_Base.op_Array_Access
                        pst.Pulse_Checker_Prover_Base.ss t)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "Pulse.Checker.Prover.IntroPure.fst"
                       (Prims.of_int (219)) (Prims.of_int (13))
                       (Prims.of_int (219)) (Prims.of_int (23)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "Pulse.Checker.Prover.IntroPure.fst"
                       (Prims.of_int (221)) (Prims.of_int (2))
                       (Prims.of_int (360)) (Prims.of_int (14)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 (fun t_ss ->
                    let uu___2 =
                      Pulse_Checker_Prover_Util.debug_prover
                        pst.Pulse_Checker_Prover_Base.pg
                        (fun uu___3 ->
                           let uu___4 =
                             Pulse_Typing_Env.env_to_string
                               pst.Pulse_Checker_Prover_Base.uvs in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.IntroPure.fst"
                                      (Prims.of_int (224)) (Prims.of_int (6))
                                      (Prims.of_int (224))
                                      (Prims.of_int (29)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.IntroPure.fst"
                                      (Prims.of_int (222)) (Prims.of_int (4))
                                      (Prims.of_int (224))
                                      (Prims.of_int (29)))))
                             (Obj.magic uu___4)
                             (fun uu___5 ->
                                (fun uu___5 ->
                                   let uu___6 =
                                     let uu___7 =
                                       Pulse_Syntax_Printer.term_to_string
                                         t_ss in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Prover.IntroPure.fst"
                                                (Prims.of_int (223))
                                                (Prims.of_int (6))
                                                (Prims.of_int (223))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Printf.fst"
                                                (Prims.of_int (122))
                                                (Prims.of_int (8))
                                                (Prims.of_int (124))
                                                (Prims.of_int (44)))))
                                       (Obj.magic uu___7)
                                       (fun uu___8 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___9 ->
                                               fun x ->
                                                 Prims.strcat
                                                   (Prims.strcat
                                                      "Intro pure trying to typecheck prop: "
                                                      (Prims.strcat uu___8
                                                         " with uvs: "))
                                                   (Prims.strcat x "\n"))) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.IntroPure.fst"
                                                 (Prims.of_int (222))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (224))
                                                 (Prims.of_int (29)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.IntroPure.fst"
                                                 (Prims.of_int (222))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (224))
                                                 (Prims.of_int (29)))))
                                        (Obj.magic uu___6)
                                        (fun uu___7 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___8 -> uu___7 uu___5))))
                                  uu___5)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.IntroPure.fst"
                                  (Prims.of_int (221)) (Prims.of_int (2))
                                  (Prims.of_int (224)) (Prims.of_int (30)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.IntroPure.fst"
                                  (Prims.of_int (224)) (Prims.of_int (31))
                                  (Prims.of_int (360)) (Prims.of_int (14)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun uu___3 ->
                               let uu___4 =
                                 try_collect_substs
                                   pst.Pulse_Checker_Prover_Base.uvs t_ss in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.IntroPure.fst"
                                             (Prims.of_int (227))
                                             (Prims.of_int (12))
                                             (Prims.of_int (227))
                                             (Prims.of_int (43)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.IntroPure.fst"
                                             (Prims.of_int (228))
                                             (Prims.of_int (51))
                                             (Prims.of_int (360))
                                             (Prims.of_int (14)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun ss' ->
                                          let uu___5 =
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___6 ->
                                                    Pulse_Checker_Prover_Substs.push_ss
                                                      pst.Pulse_Checker_Prover_Base.ss
                                                      ss')) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.IntroPure.fst"
                                                        (Prims.of_int (229))
                                                        (Prims.of_int (15))
                                                        (Prims.of_int (229))
                                                        (Prims.of_int (36)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.IntroPure.fst"
                                                        (Prims.of_int (230))
                                                        (Prims.of_int (38))
                                                        (Prims.of_int (360))
                                                        (Prims.of_int (14)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  (fun ss_new ->
                                                     let uu___6 =
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___7 ->
                                                               Pulse_Checker_Prover_Base.op_Array_Access
                                                                 ss_new t)) in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.IntroPure.fst"
                                                                   (Prims.of_int (232))
                                                                   (Prims.of_int (13))
                                                                   (Prims.of_int (232))
                                                                   (Prims.of_int (23)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.IntroPure.fst"
                                                                   (Prims.of_int (232))
                                                                   (Prims.of_int (26))
                                                                   (Prims.of_int (360))
                                                                   (Prims.of_int (14)))))
                                                          (Obj.magic uu___6)
                                                          (fun uu___7 ->
                                                             (fun t_ss1 ->
                                                                let uu___7 =
                                                                  let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Syntax_Naming.freevars
                                                                    t_ss1)) in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (27)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (31)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    (fun fvs
                                                                    ->
                                                                    if
                                                                    Pulse_Typing_Env.check_disjoint
                                                                    pst.Pulse_Checker_Prover_Base.uvs
                                                                    fvs
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ())))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    t_ss1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStarC_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Could not resolve all free variables in the proposition:")
                                                                    uu___13)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    [uu___12])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t_ss1))
                                                                    uu___11))
                                                                    uu___11))))
                                                                    uu___9) in
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    Pulse_Checker_Pure.core_check_tot_term
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    t_ss1
                                                                    Pulse_Typing.tm_prop in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun d ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_V2_Derived.with_policy
                                                                    FStarC_Tactics_Types.ForceSMT
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Checker_Pure.check_prop_validity
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    t_ss1 ()) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    d_valid
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing_Env.fresh
                                                                    (Pulse_Typing_Env.push_env
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst.Pulse_Checker_Prover_Base.uvs))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun x ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.tm_pure
                                                                    t)
                                                                    pst.Pulse_Checker_Prover_Base.solved)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    solved_new
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    unsolved')) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    unsolved_new
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    ss_new
                                                                    pst.Pulse_Checker_Prover_Base.solved))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (90)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    frame ->
                                                                    let uu___16
                                                                    =
                                                                    k_intro_pure
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    t_ss1 ()
                                                                    () frame in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    k_pure ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Pulse_Checker_Base.k_elab_trans
                                                                    preamble.Pulse_Checker_Prover_Base.g0
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    ss_new
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    ss_new
                                                                    solved_new))
                                                                    (coerce_eq
                                                                    pst.Pulse_Checker_Prover_Base.k
                                                                    ())
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    frame
                                                                    frame
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    frame
                                                                    (Pulse_Syntax_Pure.tm_pure
                                                                    t_ss1))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.tm_pure
                                                                    t_ss1)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    ss_new
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    k_pure ()
                                                                    ())))))
                                                                    uu___16) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun k ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Checker_Prover_Base.pg
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.pg);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.remaining_ctxt);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.uvs
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.uvs);
                                                                    Pulse_Checker_Prover_Base.ss
                                                                    = ss_new;
                                                                    Pulse_Checker_Prover_Base.nts
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Checker_Prover_Base.solved
                                                                    =
                                                                    solved_new;
                                                                    Pulse_Checker_Prover_Base.unsolved
                                                                    =
                                                                    unsolved_new;
                                                                    Pulse_Checker_Prover_Base.k
                                                                    = k;
                                                                    Pulse_Checker_Prover_Base.goals_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.solved_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.progress
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.progress);
                                                                    Pulse_Checker_Prover_Base.allow_ambiguous
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                                                                    }))))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                               uu___7)))
                                                    uu___6))) uu___5)))
                              uu___3))) uu___2)