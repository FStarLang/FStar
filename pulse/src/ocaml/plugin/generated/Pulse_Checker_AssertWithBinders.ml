open Prims
let (is_host_term : FStar_Reflection_Types.term -> Prims.bool) =
  fun t ->
    Prims.op_Negation
      (FStar_Reflection_V2_Data.uu___is_Tv_Unknown
         (FStar_Reflection_V2_Builtins.inspect_ln t))
let (debug_log :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  = Pulse_Checker_Common.debug_log "with_binders"
let (instantiate_binders_with_uvars :
  FStar_Reflection_Types.term ->
    (((Pulse_Checker_Inference.uvar * Pulse_Syntax_Base.term) Prims.list *
       Pulse_Syntax_Base.vprop),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun top ->
    let rec aux uu___1 uu___ =
      (fun uvars ->
         fun t ->
           match FStar_Reflection_V2_Builtins.inspect_ln t with
           | FStar_Reflection_V2_Data.Tv_Unknown ->
               Obj.magic
                 (Obj.repr (FStar_Tactics_V2_Derived.fail "Impossible"))
           | FStar_Reflection_V2_Data.Tv_Abs (b, body) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (26)) (Prims.of_int (21))
                                (Prims.of_int (26)) (Prims.of_int (39)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (26)) (Prims.of_int (42))
                                (Prims.of_int (30)) (Prims.of_int (26)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             FStar_Reflection_V2_Builtins.inspect_binder b))
                       (fun uu___ ->
                          (fun bv ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.AssertWithBinders.fst"
                                           (Prims.of_int (27))
                                           (Prims.of_int (24))
                                           (Prims.of_int (27))
                                           (Prims.of_int (79)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.AssertWithBinders.fst"
                                           (Prims.of_int (27))
                                           (Prims.of_int (16))
                                           (Prims.of_int (27))
                                           (Prims.of_int (21)))))
                                  (Obj.magic
                                     (Pulse_Checker_Inference.gen_uvar
                                        (Pulse_Syntax_Base.mk_ppname
                                           bv.FStar_Reflection_V2_Data.ppname2
                                           (Pulse_RuntimeUtils.range_of_term
                                              t))))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        match uu___ with
                                        | (uv, t1) ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (28))
                                                          (Prims.of_int (24))
                                                          (Prims.of_int (28))
                                                          (Prims.of_int (38)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (28))
                                                          (Prims.of_int (41))
                                                          (Prims.of_int (30))
                                                          (Prims.of_int (26)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 -> (uv, t1)
                                                       :: uvars))
                                                 (fun uu___1 ->
                                                    (fun uvars1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (63)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (26)))))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___1 ->
                                                                  FStar_Reflection_Typing.subst_term
                                                                    body
                                                                    (
                                                                    Pulse_Syntax_Naming.rt_subst
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    t1)])))
                                                            (fun uu___1 ->
                                                               (fun body1 ->
                                                                  Obj.magic
                                                                    (
                                                                    aux
                                                                    uvars1
                                                                    body1))
                                                                 uu___1)))
                                                      uu___1))) uu___)))
                            uu___)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (match Pulse_Readback.readback_ty t with
                     | FStar_Pervasives_Native.None ->
                         FStar_Tactics_V2_Derived.fail
                           "Failed to readback elaborated assertion"
                     | FStar_Pervasives_Native.Some t1 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              ((FStar_List_Tot_Base.rev uvars), t1)))))
        uu___1 uu___ in
    aux [] top
let (infer_binder_types :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.binder Prims.list ->
      Pulse_Syntax_Base.vprop ->
        (((Pulse_Checker_Inference.uvar * Pulse_Syntax_Base.term) Prims.list
           * Pulse_Syntax_Base.vprop),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun bs ->
      fun v ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (40)) (Prims.of_int (13))
                   (Prims.of_int (40)) (Prims.of_int (24)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (41)) (Prims.of_int (4)) (Prims.of_int (66))
                   (Prims.of_int (31)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Elaborate_Pure.elab_term v))
          (fun uu___ ->
             (fun tv ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.AssertWithBinders.fst"
                              (Prims.of_int (41)) (Prims.of_int (4))
                              (Prims.of_int (42)) (Prims.of_int (94)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.AssertWithBinders.fst"
                              (Prims.of_int (42)) (Prims.of_int (95))
                              (Prims.of_int (66)) (Prims.of_int (31)))))
                     (if Prims.op_Negation (is_host_term tv)
                      then
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.AssertWithBinders.fst"
                                         (Prims.of_int (42))
                                         (Prims.of_int (31))
                                         (Prims.of_int (42))
                                         (Prims.of_int (94)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.AssertWithBinders.fst"
                                         (Prims.of_int (42))
                                         (Prims.of_int (9))
                                         (Prims.of_int (42))
                                         (Prims.of_int (94)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (42))
                                               (Prims.of_int (73))
                                               (Prims.of_int (42))
                                               (Prims.of_int (93)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "prims.fst"
                                               (Prims.of_int (590))
                                               (Prims.of_int (19))
                                               (Prims.of_int (590))
                                               (Prims.of_int (31)))))
                                      (Obj.magic
                                         (Pulse_Syntax_Printer.term_to_string
                                            v))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              Prims.strcat
                                                "Cannot infer type of "
                                                (Prims.strcat uu___ "")))))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      Obj.magic
                                        (Pulse_Typing_Env.fail g
                                           (FStar_Pervasives_Native.Some
                                              (v.Pulse_Syntax_Base.range1))
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
                                         "Pulse.Checker.AssertWithBinders.fst"
                                         (Prims.of_int (44))
                                         (Prims.of_int (8))
                                         (Prims.of_int (50))
                                         (Prims.of_int (22)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.AssertWithBinders.fst"
                                         (Prims.of_int (51))
                                         (Prims.of_int (6))
                                         (Prims.of_int (66))
                                         (Prims.of_int (31)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      fun b ->
                                        FStar_Reflection_V2_Builtins.pack_binder
                                          {
                                            FStar_Reflection_V2_Data.sort2 =
                                              (Pulse_Elaborate_Pure.elab_term
                                                 b.Pulse_Syntax_Base.binder_ty);
                                            FStar_Reflection_V2_Data.qual =
                                              FStar_Reflection_V2_Data.Q_Explicit;
                                            FStar_Reflection_V2_Data.attrs =
                                              [];
                                            FStar_Reflection_V2_Data.ppname2
                                              =
                                              ((b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name)
                                          }))
                                (fun uu___1 ->
                                   (fun as_binder ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                    (Prims.of_int (53))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (58))
                                                    (Prims.of_int (14)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                    (Prims.of_int (59))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (66))
                                                    (Prims.of_int (31)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 FStar_List_Tot_Base.fold_right
                                                   (fun b ->
                                                      fun tv1 ->
                                                        FStar_Reflection_V2_Builtins.pack_ln
                                                          (FStar_Reflection_V2_Data.Tv_Abs
                                                             ((as_binder b),
                                                               tv1))) bs tv))
                                           (fun uu___1 ->
                                              (fun abstraction ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (61))
                                                               (Prims.of_int (30))
                                                               (Prims.of_int (61))
                                                               (Prims.of_int (92)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (59))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (66))
                                                               (Prims.of_int (31)))))
                                                      (Obj.magic
                                                         (Pulse_Checker_Pure.instantiate_term_implicits
                                                            g
                                                            (Pulse_Syntax_Base.tm_fstar
                                                               abstraction
                                                               v.Pulse_Syntax_Base.range1)))
                                                      (fun uu___1 ->
                                                         (fun uu___1 ->
                                                            match uu___1 with
                                                            | (inst_abstraction,
                                                               uu___2) ->
                                                                (match 
                                                                   inst_abstraction.Pulse_Syntax_Base.t
                                                                 with
                                                                 | Pulse_Syntax_Base.Tm_FStar
                                                                    t ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (instantiate_binders_with_uvars
                                                                    t))
                                                                 | uu___3 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Impossible"))))
                                                           uu___1))) uu___1)))
                                     uu___1))) uu___))) uu___)
let option_must :
  'a .
    'a FStar_Pervasives_Native.option ->
      Prims.string -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun msg ->
           match f with
           | FStar_Pervasives_Native.Some x ->
               Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x))
           | FStar_Pervasives_Native.None ->
               Obj.magic (FStar_Tactics_V2_Derived.fail msg)) uu___1 uu___
let (unfold_head :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           match t.Pulse_Syntax_Base.t with
           | Pulse_Syntax_Base.Tm_FStar rt ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (77)) (Prims.of_int (20))
                                (Prims.of_int (77)) (Prims.of_int (36)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (76)) (Prims.of_int (21))
                                (Prims.of_int (89)) (Prims.of_int (5)))))
                       (Obj.magic
                          (FStar_Tactics_V2_SyntaxHelpers.collect_app rt))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | (head, uu___1) ->
                                 (match FStar_Reflection_V2_Builtins.inspect_ln
                                          head
                                  with
                                  | FStar_Reflection_V2_Data.Tv_FVar fv ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                    (Prims.of_int (81))
                                                    (Prims.of_int (17))
                                                    (Prims.of_int (81))
                                                    (Prims.of_int (85)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                    (Prims.of_int (81))
                                                    (Prims.of_int (88))
                                                    (Prims.of_int (85))
                                                    (Prims.of_int (10)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 Pulse_RuntimeUtils.unfold_def
                                                   (Pulse_Typing_Env.fstar_env
                                                      g)
                                                   (FStar_String.concat "."
                                                      (FStar_Reflection_V2_Builtins.inspect_fv
                                                         fv)) rt))
                                           (fun uu___2 ->
                                              (fun rt1 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (82))
                                                               (Prims.of_int (17))
                                                               (Prims.of_int (82))
                                                               (Prims.of_int (83)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (82))
                                                               (Prims.of_int (86))
                                                               (Prims.of_int (85))
                                                               (Prims.of_int (10)))))
                                                      (Obj.magic
                                                         (option_must rt1
                                                            "Unexpected: reduction produced an ill-formed term"))
                                                      (fun uu___2 ->
                                                         (fun rt2 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (92)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (10)))))
                                                                 (Obj.magic
                                                                    (
                                                                    option_must
                                                                    (Pulse_Readback.readback_ty
                                                                    rt2)
                                                                    "Unexpected: unable to readback unfolded term"))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    (debug_log
                                                                    g
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (134)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    rt2))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (112)))))
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
                                                                    t))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Unfolded "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    " to F* term "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " and readback as "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    uu___4))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ty))))
                                                                    uu___2)))
                                                           uu___2))) uu___2))
                                  | FStar_Reflection_V2_Data.Tv_UInst
                                      (fv, uu___2) ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                    (Prims.of_int (81))
                                                    (Prims.of_int (17))
                                                    (Prims.of_int (81))
                                                    (Prims.of_int (85)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                    (Prims.of_int (81))
                                                    (Prims.of_int (88))
                                                    (Prims.of_int (85))
                                                    (Prims.of_int (10)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 ->
                                                 Pulse_RuntimeUtils.unfold_def
                                                   (Pulse_Typing_Env.fstar_env
                                                      g)
                                                   (FStar_String.concat "."
                                                      (FStar_Reflection_V2_Builtins.inspect_fv
                                                         fv)) rt))
                                           (fun uu___3 ->
                                              (fun rt1 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (82))
                                                               (Prims.of_int (17))
                                                               (Prims.of_int (82))
                                                               (Prims.of_int (83)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (82))
                                                               (Prims.of_int (86))
                                                               (Prims.of_int (85))
                                                               (Prims.of_int (10)))))
                                                      (Obj.magic
                                                         (option_must rt1
                                                            "Unexpected: reduction produced an ill-formed term"))
                                                      (fun uu___3 ->
                                                         (fun rt2 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (92)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (10)))))
                                                                 (Obj.magic
                                                                    (
                                                                    option_must
                                                                    (Pulse_Readback.readback_ty
                                                                    rt2)
                                                                    "Unexpected: unable to readback unfolded term"))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    (debug_log
                                                                    g
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (134)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    rt2))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (112)))))
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
                                                                    t))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Unfolded "
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    " to F* term "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " and readback as "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6
                                                                    uu___5))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    uu___4))))
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ty))))
                                                                    uu___3)))
                                                           uu___3))) uu___3))
                                  | uu___2 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                    (Prims.of_int (88))
                                                    (Prims.of_int (30))
                                                    (Prims.of_int (88))
                                                    (Prims.of_int (86)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                    (Prims.of_int (88))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (88))
                                                    (Prims.of_int (86)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (88))
                                                          (Prims.of_int (65))
                                                          (Prims.of_int (88))
                                                          (Prims.of_int (85)))))
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
                                                       t))
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 ->
                                                         Prims.strcat
                                                           "Cannot unfold "
                                                           (Prims.strcat
                                                              uu___3 "")))))
                                           (fun uu___3 ->
                                              (fun uu___3 ->
                                                 Obj.magic
                                                   (Pulse_Typing_Env.fail g
                                                      (FStar_Pervasives_Native.Some
                                                         (t.Pulse_Syntax_Base.range1))
                                                      uu___3)) uu___3))))
                            uu___)))
           | uu___ ->
               Obj.magic
                 (Obj.repr (FStar_Tactics_V2_Derived.fail "Impossible")))
        uu___1 uu___
let (prepare_goal :
  Pulse_Syntax_Base.proof_hint_type ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun hint_type ->
           fun g ->
             fun v ->
               match hint_type with
               | Pulse_Syntax_Base.ASSERT ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> v)))
               | Pulse_Syntax_Base.UNFOLD ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> v)))
               | Pulse_Syntax_Base.FOLD ->
                   Obj.magic (Obj.repr (unfold_head g v))) uu___2 uu___1
          uu___
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Checker_Common.post_hint_opt ->
            Pulse_Checker_Common.check_t ->
              ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun st ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun check1 ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.AssertWithBinders.fst"
                         (Prims.of_int (107)) (Prims.of_int (68))
                         (Prims.of_int (107)) (Prims.of_int (75)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.AssertWithBinders.fst"
                         (Prims.of_int (107)) (Prims.of_int (3))
                         (Prims.of_int (149)) (Prims.of_int (38)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> st.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                          { Pulse_Syntax_Base.hint_type = hint_type;
                            Pulse_Syntax_Base.binders = binders;
                            Pulse_Syntax_Base.v = v;
                            Pulse_Syntax_Base.t4 = body;_}
                          ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.AssertWithBinders.fst"
                                        (Prims.of_int (108))
                                        (Prims.of_int (17))
                                        (Prims.of_int (108))
                                        (Prims.of_int (47)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.AssertWithBinders.fst"
                                        (Prims.of_int (107))
                                        (Prims.of_int (78))
                                        (Prims.of_int (149))
                                        (Prims.of_int (38)))))
                               (Obj.magic (infer_binder_types g binders v))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | (uvs, v1) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.AssertWithBinders.fst"
                                                       (Prims.of_int (109))
                                                       (Prims.of_int (15))
                                                       (Prims.of_int (109))
                                                       (Prims.of_int (41)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.AssertWithBinders.fst"
                                                       (Prims.of_int (110))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (149))
                                                       (Prims.of_int (38)))))
                                              (Obj.magic
                                                 (prepare_goal hint_type g v1))
                                              (fun uu___2 ->
                                                 (fun goal ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                                  (Prims.of_int (110))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (110))
                                                                  (Prims.of_int (130)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                                  (Prims.of_int (110))
                                                                  (Prims.of_int (131))
                                                                  (Prims.of_int (149))
                                                                  (Prims.of_int (38)))))
                                                         (Obj.magic
                                                            (debug_log g
                                                               (fun uu___2 ->
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (129)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (129)))))
                                                                    (
                                                                    Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    pre))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (129)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (129)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (106)))))
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
                                                                    goal))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Trying to solve "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " \nagainst context "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                    uu___3))))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (74)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (38)))))
                                                                    (
                                                                    Obj.magic
                                                                    (Pulse_Checker_Inference.try_inst_uvs_in_goal
                                                                    g pre
                                                                    goal))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    solution
                                                                    ->
                                                                    match 
                                                                    Pulse_Checker_Inference.unsolved
                                                                    solution
                                                                    uvs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uvs1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (116))
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (96)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (uu___4,
                                                                    t) ->
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    t) uvs1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_String.concat
                                                                    ", "
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "Could not instantiate "
                                                                    (Prims.strcat
                                                                    uu___3 "")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.range2))
                                                                    uu___3))
                                                                    uu___3))
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (debug_log
                                                                    g
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.solutions_to_string
                                                                    solution))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Solution: "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (15)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.fold_left
                                                                    (fun
                                                                    subst ->
                                                                    fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (uv, t)
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solution
                                                                    t))
                                                                    (fun sol
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    sol)) ::
                                                                    (Pulse_Syntax_Naming.shift_subst
                                                                    subst))))
                                                                    [] uvs))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun sub
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun lhs
                                                                    ->
                                                                    fun rhs
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t1
                                                                    = lhs;
                                                                    Pulse_Syntax_Base.t2
                                                                    = rhs
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2)
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun rw
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body sub))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    body' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    (Pulse_Typing.as_binder
                                                                    (Pulse_Syntax_Base.tm_fstar
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])))
                                                                    st.Pulse_Syntax_Base.range2));
                                                                    Pulse_Syntax_Base.head1
                                                                    = rw;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body'
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
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    = tm;
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2)
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun tm1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (106)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (debug_log
                                                                    g
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (105)))))
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
                                                                    tm1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    "After unfold: about to check "
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (check1 g
                                                                    tm1 pre
                                                                    ()
                                                                    post_hint))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    rewrite_and_check
                                                                    ->
                                                                    match hint_type
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.ASSERT
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body sub))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    body' ->
                                                                    Obj.magic
                                                                    (check1 g
                                                                    body' pre
                                                                    ()
                                                                    post_hint))
                                                                    uu___5))
                                                                    | 
                                                                    Pulse_Syntax_Base.UNFOLD
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solution
                                                                    v1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun v2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (unfold_head
                                                                    g v2))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    unfolded_v
                                                                    ->
                                                                    Obj.magic
                                                                    (rewrite_and_check
                                                                    v2
                                                                    unfolded_v))
                                                                    uu___5)))
                                                                    uu___5))
                                                                    | 
                                                                    Pulse_Syntax_Base.FOLD
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solution
                                                                    v1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun v2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solution
                                                                    goal))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    unfolded_v
                                                                    ->
                                                                    Obj.magic
                                                                    (rewrite_and_check
                                                                    unfolded_v
                                                                    v2))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                              uu___2)))
                                                   uu___2))) uu___1))) uu___)