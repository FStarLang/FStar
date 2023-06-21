open Prims
let (is_host_term : FStar_Reflection_Types.term -> Prims.bool) =
  fun t ->
    Prims.op_Negation
      (FStar_Reflection_V2_Data.uu___is_Tv_Unknown
         (FStar_Reflection_V2_Builtins.inspect_ln t))
let (infer_binder_types :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.binder Prims.list ->
      Pulse_Syntax_Base.vprop ->
        (((Pulse_Syntax_Base.binder * FStar_Tactics_NamedView.binder)
           Prims.list * Pulse_Syntax_Base.vprop),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun bs ->
      fun v ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (18)) (Prims.of_int (13))
                   (Prims.of_int (18)) (Prims.of_int (24)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (19)) (Prims.of_int (4)) (Prims.of_int (46))
                   (Prims.of_int (48)))))
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
                              (Prims.of_int (19)) (Prims.of_int (4))
                              (Prims.of_int (20)) (Prims.of_int (94)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.AssertWithBinders.fst"
                              (Prims.of_int (20)) (Prims.of_int (95))
                              (Prims.of_int (46)) (Prims.of_int (48)))))
                     (if Prims.op_Negation (is_host_term tv)
                      then
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.AssertWithBinders.fst"
                                         (Prims.of_int (20))
                                         (Prims.of_int (31))
                                         (Prims.of_int (20))
                                         (Prims.of_int (94)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.AssertWithBinders.fst"
                                         (Prims.of_int (20))
                                         (Prims.of_int (9))
                                         (Prims.of_int (20))
                                         (Prims.of_int (94)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (20))
                                               (Prims.of_int (73))
                                               (Prims.of_int (20))
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
                                         (Prims.of_int (22))
                                         (Prims.of_int (8))
                                         (Prims.of_int (28))
                                         (Prims.of_int (22)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.AssertWithBinders.fst"
                                         (Prims.of_int (29))
                                         (Prims.of_int (6))
                                         (Prims.of_int (46))
                                         (Prims.of_int (48)))))
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
                                                    (Prims.of_int (31))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (36))
                                                    (Prims.of_int (14)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                    (Prims.of_int (37))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (46))
                                                    (Prims.of_int (48)))))
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
                                                               (Prims.of_int (38))
                                                               (Prims.of_int (30))
                                                               (Prims.of_int (38))
                                                               (Prims.of_int (92)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (37))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (46))
                                                               (Prims.of_int (48)))))
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
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (48)))))
                                                                    (match 
                                                                    inst_abstraction.Pulse_Syntax_Base.t
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_FStar
                                                                    t ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_SyntaxHelpers.collect_abs
                                                                    t))
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Impossible")))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (formals,
                                                                    body) ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (is_host_term
                                                                    body)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Impossible"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.zip
                                                                    bs
                                                                    formals))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (uu___5,
                                                                    (Pulse_Syntax_Base.tm_fstar
                                                                    body
                                                                    v.Pulse_Syntax_Base.range1)))))))
                                                                    uu___3)))
                                                           uu___1))) uu___1)))
                                     uu___1))) uu___))) uu___)
let (instantiate_binders :
  (Pulse_Syntax_Base.binder * FStar_Tactics_NamedView.binder) Prims.list ->
    Pulse_Syntax_Base.vprop ->
      (((Pulse_Checker_Inference.uvar * Pulse_Syntax_Base.term) Prims.list *
         Pulse_Syntax_Base.vprop),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun v ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                 (Prims.of_int (50)) (Prims.of_int (41)) (Prims.of_int (50))
                 (Prims.of_int (47)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                 (Prims.of_int (50)) (Prims.of_int (50)) (Prims.of_int (59))
                 (Prims.of_int (27)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> fun x -> x.FStar_Tactics_NamedView.uniq))
        (fun uu___ ->
           (fun binder_uniq ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.AssertWithBinders.fst"
                            (Prims.of_int (52)) (Prims.of_int (8))
                            (Prims.of_int (56)) (Prims.of_int (14)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.AssertWithBinders.fst"
                            (Prims.of_int (57)) (Prims.of_int (6))
                            (Prims.of_int (59)) (Prims.of_int (27)))))
                   (Obj.magic
                      (FStar_Tactics_Util.map
                         (fun uu___ ->
                            match uu___ with
                            | (b, tb) ->
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.AssertWithBinders.fst"
                                           (Prims.of_int (54))
                                           (Prims.of_int (28))
                                           (Prims.of_int (54))
                                           (Prims.of_int (56)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.AssertWithBinders.fst"
                                           (Prims.of_int (53))
                                           (Prims.of_int (26))
                                           (Prims.of_int (55))
                                           (Prims.of_int (48)))))
                                  (Obj.magic
                                     (Pulse_Checker_Inference.gen_uvar
                                        b.Pulse_Syntax_Base.binder_ppname))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          match uu___1 with
                                          | (uv, t) ->
                                              ((uv, t),
                                                (Pulse_Syntax_Naming.NT
                                                   ((binder_uniq tb), t))))))
                         bs))
                   (fun uvs_subst ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           match FStar_List_Tot_Base.unzip uvs_subst with
                           | (uvs, subst) ->
                               (uvs,
                                 (Pulse_Syntax_Naming.subst_term v subst))))))
             uu___)
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
                         (Prims.of_int (69)) (Prims.of_int (54))
                         (Prims.of_int (69)) (Prims.of_int (61)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.AssertWithBinders.fst"
                         (Prims.of_int (69)) (Prims.of_int (3))
                         (Prims.of_int (88)) (Prims.of_int (43)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> st.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_AssertWithBinders
                          { Pulse_Syntax_Base.binders = binders;
                            Pulse_Syntax_Base.v = v;
                            Pulse_Syntax_Base.t4 = body;_}
                          ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.AssertWithBinders.fst"
                                        (Prims.of_int (70))
                                        (Prims.of_int (23))
                                        (Prims.of_int (70))
                                        (Prims.of_int (53)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.AssertWithBinders.fst"
                                        (Prims.of_int (69))
                                        (Prims.of_int (64))
                                        (Prims.of_int (88))
                                        (Prims.of_int (43)))))
                               (Obj.magic (infer_binder_types g binders v))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | (t_binders, v1) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.AssertWithBinders.fst"
                                                       (Prims.of_int (71))
                                                       (Prims.of_int (17))
                                                       (Prims.of_int (71))
                                                       (Prims.of_int (48)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.AssertWithBinders.fst"
                                                       (Prims.of_int (70))
                                                       (Prims.of_int (56))
                                                       (Prims.of_int (88))
                                                       (Prims.of_int (43)))))
                                              (Obj.magic
                                                 (instantiate_binders
                                                    t_binders v1))
                                              (fun uu___2 ->
                                                 (fun uu___2 ->
                                                    match uu___2 with
                                                    | (uvs, v2) ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (71)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (43)))))
                                                             (Obj.magic
                                                                (Pulse_Checker_Inference.try_inst_uvs_in_goal
                                                                   g pre v2))
                                                             (fun uu___3 ->
                                                                (fun solution
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
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (77))
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
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (77))
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
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.fold_right
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun
                                                                    uu___5 ->
                                                                    match 
                                                                    (uu___4,
                                                                    uu___5)
                                                                    with
                                                                    | 
                                                                    ((uv, t),
                                                                    (index,
                                                                    subst))
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solution
                                                                    t))
                                                                    (fun sol
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    ((index +
                                                                    Prims.int_one),
                                                                    ((Pulse_Syntax_Naming.DT
                                                                    (index,
                                                                    sol)) ::
                                                                    subst)))))
                                                                    uvs
                                                                    (Prims.int_zero,
                                                                    [])))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (uu___5,
                                                                    body_subst)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    body_subst))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (check1 g
                                                                    body1 pre
                                                                    ()
                                                                    post_hint))
                                                                    uu___6)))
                                                                    uu___4)))
                                                                  uu___3)))
                                                   uu___2))) uu___1))) uu___)