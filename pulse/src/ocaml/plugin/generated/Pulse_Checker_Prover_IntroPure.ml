open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (k_intro_pure :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        (unit, unit) Pulse_Typing.prop_validity ->
          Pulse_Syntax_Base.vprop ->
            ((unit, unit, unit, unit)
               Pulse_Checker_Base.continuation_elaborator,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      fun d ->
        fun token ->
          fun frame ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "Pulse.Checker.Prover.IntroPure.fst"
                       (Prims.of_int (25)) (Prims.of_int (10))
                       (Prims.of_int (25)) (Prims.of_int (50)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "Pulse.Checker.Prover.IntroPure.fst"
                       (Prims.of_int (25)) (Prims.of_int (53))
                       (Prims.of_int (59)) (Prims.of_int (30)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Pulse_Typing.wtag
                      (FStar_Pervasives_Native.Some
                         Pulse_Syntax_Base.STT_Ghost)
                      (Pulse_Syntax_Base.Tm_IntroPure
                         { Pulse_Syntax_Base.p3 = p })))
              (fun uu___ ->
                 (fun t ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.IntroPure.fst"
                                  (Prims.of_int (26)) (Prims.of_int (10))
                                  (Prims.of_int (26)) (Prims.of_int (27)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.IntroPure.fst"
                                  (Prims.of_int (26)) (Prims.of_int (30))
                                  (Prims.of_int (59)) (Prims.of_int (30)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> Pulse_Typing.comp_intro_pure p))
                         (fun uu___ ->
                            (fun c ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.IntroPure.fst"
                                             (Prims.of_int (27))
                                             (Prims.of_int (28))
                                             (Prims.of_int (27))
                                             (Prims.of_int (51)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.IntroPure.fst"
                                             (Prims.of_int (27))
                                             (Prims.of_int (54))
                                             (Prims.of_int (59))
                                             (Prims.of_int (30)))))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          Pulse_Typing.T_IntroPure
                                            (g, p, (), token)))
                                    (fun uu___ ->
                                       (fun d1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.IntroPure.fst"
                                                        (Prims.of_int (29))
                                                        (Prims.of_int (10))
                                                        (Prims.of_int (29))
                                                        (Prims.of_int (17)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.IntroPure.fst"
                                                        (Prims.of_int (32))
                                                        (Prims.of_int (30))
                                                        (Prims.of_int (59))
                                                        (Prims.of_int (30)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___ ->
                                                     Pulse_Typing_Env.fresh g))
                                               (fun uu___ ->
                                                  (fun x ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.IntroPure.fst"
                                                                   (Prims.of_int (34))
                                                                   (Prims.of_int (15))
                                                                   (Prims.of_int (34))
                                                                   (Prims.of_int (44)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.IntroPure.fst"
                                                                   (Prims.of_int (34))
                                                                   (Prims.of_int (47))
                                                                   (Prims.of_int (59))
                                                                   (Prims.of_int (30)))))
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___ ->
                                                                Pulse_Syntax_Base.mk_ppname_no_range
                                                                  "_pintrop"))
                                                          (fun uu___ ->
                                                             (fun ppname ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.continuation_elaborator_with_bind
                                                                    g frame c
                                                                    t d1 ()
                                                                    (ppname,
                                                                    x)))
                                                                    (fun k ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    fun
                                                                    post_hint
                                                                    ->
                                                                    fun r ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    r))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t1, c1,
                                                                    d11) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    d11))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun d12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    empty_env
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Metatheory.st_typing_weakening
                                                                    g
                                                                    empty_env
                                                                    t1 c1 d12
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    Pulse_Typing.tm_unit)))
                                                                    (fun
                                                                    uu___2 ->
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
                                                                    Pulse_Syntax_Base.tm_emp)
                                                                    frame
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Base.tm_pure
                                                                    p) frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    frame
                                                                    (Pulse_Syntax_Base.tm_pure
                                                                    p)) k ()
                                                                    ()
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (t1, c1,
                                                                    d13))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___1)))))
                                                               uu___))) uu___)))
                                         uu___))) uu___))) uu___)
let (is_eq2_uvar :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) Prims.dtuple2
        FStar_Pervasives_Native.option)
  =
  fun uvs ->
    fun t ->
      match Pulse_Syntax_Pure.is_eq2 t with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (l, r) ->
          (match Pulse_Syntax_Pure.is_var l with
           | FStar_Pervasives_Native.Some nm ->
               if
                 FStar_Set.mem nm.Pulse_Syntax_Base.nm_index
                   (Pulse_Typing_Env.dom uvs)
               then
                 FStar_Pervasives_Native.Some
                   (Prims.Mkdtuple2 ((nm.Pulse_Syntax_Base.nm_index), r))
               else FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.None ->
               (match Pulse_Syntax_Pure.is_var r with
                | FStar_Pervasives_Native.Some nm ->
                    if
                      FStar_Set.mem nm.Pulse_Syntax_Base.nm_index
                        (Pulse_Typing_Env.dom uvs)
                    then
                      FStar_Pervasives_Native.Some
                        (Prims.Mkdtuple2 ((nm.Pulse_Syntax_Base.nm_index), l))
                    else FStar_Pervasives_Native.None
                | uu___ -> FStar_Pervasives_Native.None))
let rec (try_collect_substs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Checker_Prover_Substs.ss_t, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun uvs ->
         fun t ->
           match t.Pulse_Syntax_Base.t with
           | Pulse_Syntax_Base.Tm_FStar rt ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.IntroPure.fst"
                                (Prims.of_int (100)) (Prims.of_int (12))
                                (Prims.of_int (100)) (Prims.of_int (34)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.IntroPure.fst"
                                (Prims.of_int (102)) (Prims.of_int (6))
                                (Prims.of_int (119)) (Prims.of_int (26)))))
                       (Obj.magic
                          (FStar_Reflection_V2_Formula.term_as_formula' rt))
                       (fun uu___ ->
                          (fun f ->
                             match f with
                             | FStar_Reflection_V2_Formula.And (rt0, rt1) ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.IntroPure.fst"
                                                  (Prims.of_int (105))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (105))
                                                  (Prims.of_int (75)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.IntroPure.fst"
                                                  (Prims.of_int (105))
                                                  (Prims.of_int (78))
                                                  (Prims.of_int (111))
                                                  (Prims.of_int (21)))))
                                         (Obj.magic
                                            (try_collect_substs uvs
                                               (Pulse_Syntax_Base.tm_fstar
                                                  rt0 FStar_Range.range_0)))
                                         (fun uu___ ->
                                            (fun ss0 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.IntroPure.fst"
                                                             (Prims.of_int (106))
                                                             (Prims.of_int (18))
                                                             (Prims.of_int (106))
                                                             (Prims.of_int (75)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.IntroPure.fst"
                                                             (Prims.of_int (107))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (111))
                                                             (Prims.of_int (21)))))
                                                    (Obj.magic
                                                       (try_collect_substs
                                                          uvs
                                                          (Pulse_Syntax_Base.tm_fstar
                                                             rt1
                                                             FStar_Range.range_0)))
                                                    (fun ss1 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___ ->
                                                            if
                                                              Pulse_Checker_Prover_Substs.check_disjoint
                                                                ss0 ss1
                                                            then
                                                              Pulse_Checker_Prover_Substs.push_ss
                                                                ss0 ss1
                                                            else
                                                              Pulse_Checker_Prover_Substs.empty))))
                                              uu___)))
                             | uu___ ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            match is_eq2_uvar uvs t with
                                            | FStar_Pervasives_Native.Some
                                                (Prims.Mkdtuple2 (uv, e)) ->
                                                Pulse_Checker_Prover_Substs.push
                                                  Pulse_Checker_Prover_Substs.empty
                                                  uv e
                                            | FStar_Pervasives_Native.None ->
                                                Pulse_Checker_Prover_Substs.empty))))
                            uu___)))
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
        Pulse_Syntax_Base.vprop Prims.list ->
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
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "Pulse.Checker.Prover.IntroPure.fst"
                       (Prims.of_int (130)) (Prims.of_int (13))
                       (Prims.of_int (130)) (Prims.of_int (23)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "Pulse.Checker.Prover.IntroPure.fst"
                       (Prims.of_int (132)) (Prims.of_int (2))
                       (Prims.of_int (261)) (Prims.of_int (14)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    Pulse_Checker_Prover_Base.op_Array_Access
                      pst.Pulse_Checker_Prover_Base.ss t))
              (fun uu___1 ->
                 (fun t_ss ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.IntroPure.fst"
                                  (Prims.of_int (132)) (Prims.of_int (2))
                                  (Prims.of_int (135)) (Prims.of_int (30)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.IntroPure.fst"
                                  (Prims.of_int (135)) (Prims.of_int (31))
                                  (Prims.of_int (261)) (Prims.of_int (14)))))
                         (Obj.magic
                            (Pulse_Checker_Prover_Util.debug_prover
                               pst.Pulse_Checker_Prover_Base.pg
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.IntroPure.fst"
                                             (Prims.of_int (135))
                                             (Prims.of_int (6))
                                             (Prims.of_int (135))
                                             (Prims.of_int (29)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.IntroPure.fst"
                                             (Prims.of_int (133))
                                             (Prims.of_int (4))
                                             (Prims.of_int (135))
                                             (Prims.of_int (29)))))
                                    (Obj.magic
                                       (Pulse_Typing_Env.env_to_string
                                          pst.Pulse_Checker_Prover_Base.uvs))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.IntroPure.fst"
                                                        (Prims.of_int (133))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (135))
                                                        (Prims.of_int (29)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.IntroPure.fst"
                                                        (Prims.of_int (133))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (135))
                                                        (Prims.of_int (29)))))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.IntroPure.fst"
                                                              (Prims.of_int (134))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (134))
                                                              (Prims.of_int (29)))))
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
                                                           t_ss))
                                                     (fun uu___3 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             fun x ->
                                                               Prims.strcat
                                                                 (Prims.strcat
                                                                    "Intro pure trying to typecheck prop: "
                                                                    (
                                                                    Prims.strcat
                                                                    uu___3
                                                                    " with uvs: "))
                                                                 (Prims.strcat
                                                                    x "\n")))))
                                               (fun uu___3 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___4 ->
                                                       uu___3 uu___2))))
                                         uu___2))))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.IntroPure.fst"
                                             (Prims.of_int (138))
                                             (Prims.of_int (12))
                                             (Prims.of_int (138))
                                             (Prims.of_int (43)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.IntroPure.fst"
                                             (Prims.of_int (139))
                                             (Prims.of_int (51))
                                             (Prims.of_int (261))
                                             (Prims.of_int (14)))))
                                    (Obj.magic
                                       (try_collect_substs
                                          pst.Pulse_Checker_Prover_Base.uvs
                                          t_ss))
                                    (fun uu___2 ->
                                       (fun ss' ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.IntroPure.fst"
                                                        (Prims.of_int (140))
                                                        (Prims.of_int (15))
                                                        (Prims.of_int (140))
                                                        (Prims.of_int (36)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.IntroPure.fst"
                                                        (Prims.of_int (141))
                                                        (Prims.of_int (38))
                                                        (Prims.of_int (261))
                                                        (Prims.of_int (14)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     Pulse_Checker_Prover_Substs.push_ss
                                                       pst.Pulse_Checker_Prover_Base.ss
                                                       ss'))
                                               (fun uu___2 ->
                                                  (fun ss_new ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.IntroPure.fst"
                                                                   (Prims.of_int (143))
                                                                   (Prims.of_int (13))
                                                                   (Prims.of_int (143))
                                                                   (Prims.of_int (23)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.IntroPure.fst"
                                                                   (Prims.of_int (143))
                                                                   (Prims.of_int (26))
                                                                   (Prims.of_int (261))
                                                                   (Prims.of_int (14)))))
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                Pulse_Checker_Prover_Base.op_Array_Access
                                                                  ss_new t))
                                                          (fun uu___2 ->
                                                             (fun t_ss1 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.core_check_tot_term_with_expected_type
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    t_ss1
                                                                    Pulse_Typing.tm_prop))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_prop_validity
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    t_ss1 ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    d_valid
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    (Pulse_Typing_Env.push_env
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst.Pulse_Checker_Prover_Base.uvs)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Base.tm_pure
                                                                    t)
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    solved_new
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    unsolved'))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    unsolved_new
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    ss_new
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    frame ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroPure.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (k_intro_pure
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    t_ss1 ()
                                                                    d_valid
                                                                    frame))
                                                                    (fun
                                                                    k_pure ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Checker_Base.k_elab_trans
                                                                    preamble.Pulse_Checker_Prover_Base.g0
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    ss_new
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
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
                                                                    (Pulse_Syntax_Base.tm_pure
                                                                    t_ss1))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Base.tm_pure
                                                                    t_ss1)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    ss_new
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    k_pure ()
                                                                    ())))))
                                                                    uu___2)))
                                                                    (fun k ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
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
                                                                    = ()
                                                                    }))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                               uu___2)))
                                                    uu___2))) uu___2)))
                              uu___1))) uu___1)