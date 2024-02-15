open Prims
let (head_wild : Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders
        { Pulse_Syntax_Base.hint_type = Pulse_Syntax_Base.WILD;
          Pulse_Syntax_Base.binders = uu___; Pulse_Syntax_Base.t3 = uu___1;_}
        -> true
    | uu___ -> false
let (head_show_proof_state : Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders
        {
          Pulse_Syntax_Base.hint_type = Pulse_Syntax_Base.SHOW_PROOF_STATE
            uu___;
          Pulse_Syntax_Base.binders = uu___1;
          Pulse_Syntax_Base.t3 = uu___2;_}
        -> true
    | uu___ -> false
let (handle_head_immediately : Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun st -> (head_wild st) || (head_show_proof_state st)
let (is_host_term : FStar_Reflection_Types.term -> Prims.bool) =
  fun t ->
    Prims.op_Negation
      (FStar_Reflection_V2_Data.uu___is_Tv_Unknown
         (FStar_Reflection_V2_Builtins.inspect_ln t))
let (debug_log :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  = Pulse_Typing.debug_log "with_binders"
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
let rec (refl_abs_binders :
  FStar_Reflection_Types.term ->
    Pulse_Syntax_Base.binder Prims.list ->
      (Pulse_Syntax_Base.binder Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun acc ->
           match FStar_Reflection_V2_Builtins.inspect_ln t with
           | FStar_Reflection_V2_Data.Tv_Abs (b, body) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (50)) (Prims.of_int (25))
                                (Prims.of_int (50)) (Prims.of_int (43)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (49)) (Prims.of_int (20))
                                (Prims.of_int (55)) (Prims.of_int (75)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             FStar_Reflection_V2_Builtins.inspect_binder b))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | { FStar_Reflection_V2_Data.sort2 = sort;
                                 FStar_Reflection_V2_Data.qual = uu___1;
                                 FStar_Reflection_V2_Data.attrs = uu___2;
                                 FStar_Reflection_V2_Data.ppname2 = ppname;_}
                                 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (51))
                                               (Prims.of_int (15))
                                               (Prims.of_int (53))
                                               (Prims.of_int (33)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (54))
                                               (Prims.of_int (4))
                                               (Prims.of_int (55))
                                               (Prims.of_int (75)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.AssertWithBinders.fst"
                                                     (Prims.of_int (52))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (53))
                                                     (Prims.of_int (33)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.AssertWithBinders.fst"
                                                     (Prims.of_int (51))
                                                     (Prims.of_int (15))
                                                     (Prims.of_int (53))
                                                     (Prims.of_int (33)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.AssertWithBinders.fst"
                                                           (Prims.of_int (53))
                                                           (Prims.of_int (9))
                                                           (Prims.of_int (53))
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
                                                     (FStar_Tactics_V2_Builtins.term_to_string
                                                        sort))
                                                  (fun uu___3 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___4 ->
                                                          Prims.strcat
                                                            "Failed to readback elaborated binder sort "
                                                            (Prims.strcat
                                                               uu___3
                                                               " in refl_abs_binders")))))
                                            (fun uu___3 ->
                                               (fun uu___3 ->
                                                  Obj.magic
                                                    (option_must
                                                       (Pulse_Readback.readback_ty
                                                          sort) uu___3))
                                                 uu___3)))
                                      (fun uu___3 ->
                                         (fun sort1 ->
                                            Obj.magic
                                              (refl_abs_binders body
                                                 ((Pulse_Syntax_Base.mk_binder_ppname
                                                     sort1
                                                     (Pulse_Syntax_Base.mk_ppname
                                                        ppname
                                                        (Pulse_RuntimeUtils.range_of_term
                                                           t))) :: acc)))
                                           uu___3))) uu___)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> FStar_List_Tot_Base.rev acc)))) uu___1
        uu___
let (infer_binder_types :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.binder Prims.list ->
      Pulse_Syntax_Base.vprop ->
        (Pulse_Syntax_Base.binder Prims.list, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun bs ->
             fun v ->
               match bs with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.AssertWithBinders.fst"
                                    (Prims.of_int (63)) (Prims.of_int (12))
                                    (Prims.of_int (63)) (Prims.of_int (55)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.AssertWithBinders.fst"
                                    (Prims.of_int (63)) (Prims.of_int (58))
                                    (Prims.of_int (89)) (Prims.of_int (106)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Pulse_Typing_Env.push_context g
                                   "infer_binder_types"
                                   v.Pulse_Syntax_Base.range1))
                           (fun uu___1 ->
                              (fun g1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (64))
                                               (Prims.of_int (13))
                                               (Prims.of_int (64))
                                               (Prims.of_int (24)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (65))
                                               (Prims.of_int (4))
                                               (Prims.of_int (89))
                                               (Prims.of_int (106)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            Pulse_Elaborate_Pure.elab_term v))
                                      (fun uu___1 ->
                                         (fun tv ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (65))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (68))
                                                          (Prims.of_int (57)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (68))
                                                          (Prims.of_int (58))
                                                          (Prims.of_int (89))
                                                          (Prims.of_int (106)))))
                                                 (if
                                                    Prims.op_Negation
                                                      (is_host_term tv)
                                                  then
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (57)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (57)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (56)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (57)))))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    tv))
                                                                  (fun uu___1
                                                                    ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    v))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "assert.infer_binder_types: elaborated "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " to "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", which failed the host term check")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                                    uu___1)))
                                                            (fun uu___1 ->
                                                               (fun uu___1 ->
                                                                  Obj.magic
                                                                    (
                                                                    Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (v.Pulse_Syntax_Base.range1))
                                                                    uu___1))
                                                                 uu___1)))
                                                  else
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 -> ()))))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (20)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (106)))))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  fun b ->
                                                                    FStar_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStar_Reflection_V2_Data.sort2
                                                                    =
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    b.Pulse_Syntax_Base.binder_ty);
                                                                    FStar_Reflection_V2_Data.qual
                                                                    =
                                                                    FStar_Reflection_V2_Data.Q_Explicit;
                                                                    FStar_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStar_Reflection_V2_Data.ppname2
                                                                    =
                                                                    ((b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name)
                                                                    }))
                                                            (fun uu___2 ->
                                                               (fun as_binder
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (106)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_List_Tot_Base.fold_right
                                                                    (fun b ->
                                                                    fun tv1
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Abs
                                                                    ((as_binder
                                                                    b), tv1)))
                                                                    bs tv))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    abstraction
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (106)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.instantiate_term_implicits
                                                                    g1
                                                                    (Pulse_Syntax_Base.tm_fstar
                                                                    abstraction
                                                                    v.Pulse_Syntax_Base.range1)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (inst_abstraction,
                                                                    uu___3)
                                                                    ->
                                                                    (match 
                                                                    inst_abstraction.Pulse_Syntax_Base.t
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_FStar
                                                                    t ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (refl_abs_binders
                                                                    t []))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Impossible: instantiated abstraction is not embedded F* term, please file a bug-report"))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                 uu___2)))
                                                      uu___1))) uu___1)))
                                uu___1)))) uu___2 uu___1 uu___
let rec (open_binders :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.binder Prims.list ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.st_term ->
            ((Pulse_Typing_Env.env, Pulse_Syntax_Base.term,
               Pulse_Syntax_Base.st_term) FStar_Pervasives.dtuple3,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g ->
               fun bs ->
                 fun uvs ->
                   fun v ->
                     fun body ->
                       match bs with
                       | [] ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      FStar_Pervasives.Mkdtuple3
                                        (uvs, v, body))))
                       | b::bs1 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.AssertWithBinders.fst"
                                            (Prims.of_int (98))
                                            (Prims.of_int (12))
                                            (Prims.of_int (98))
                                            (Prims.of_int (58)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.AssertWithBinders.fst"
                                            (Prims.of_int (98))
                                            (Prims.of_int (61))
                                            (Prims.of_int (106))
                                            (Prims.of_int (77)))))
                                   (Obj.magic
                                      (Pulse_Checker_Pure.check_universe
                                         (Pulse_Typing_Env.push_env g uvs)
                                         b.Pulse_Syntax_Base.binder_ty))
                                   (fun uu___ ->
                                      (fun uu___ ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.AssertWithBinders.fst"
                                                       (Prims.of_int (99))
                                                       (Prims.of_int (12))
                                                       (Prims.of_int (99))
                                                       (Prims.of_int (34)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.AssertWithBinders.fst"
                                                       (Prims.of_int (99))
                                                       (Prims.of_int (37))
                                                       (Prims.of_int (106))
                                                       (Prims.of_int (77)))))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Pulse_Typing_Env.fresh
                                                      (Pulse_Typing_Env.push_env
                                                         g uvs)))
                                              (fun uu___1 ->
                                                 (fun x ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                                  (Prims.of_int (100))
                                                                  (Prims.of_int (13))
                                                                  (Prims.of_int (100))
                                                                  (Prims.of_int (69)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                                  (Prims.of_int (100))
                                                                  (Prims.of_int (72))
                                                                  (Prims.of_int (106))
                                                                  (Prims.of_int (77)))))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___1 ->
                                                               [Pulse_Syntax_Naming.DT
                                                                  (Prims.int_zero,
                                                                    (
                                                                    Pulse_Syntax_Pure.tm_var
                                                                    {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    =
                                                                    (b.Pulse_Syntax_Base.binder_ppname)
                                                                    }))]))
                                                         (fun uu___1 ->
                                                            (fun ss ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (45)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (77)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_List_Tot_Base.mapi
                                                                    (fun i ->
                                                                    fun b1 ->
                                                                    Pulse_Syntax_Naming.subst_binder
                                                                    b1
                                                                    (Pulse_Syntax_Naming.shift_subst_n
                                                                    i ss))
                                                                    bs1))
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    (fun bs2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Naming.subst_term
                                                                    v
                                                                    (Pulse_Syntax_Naming.shift_subst_n
                                                                    (FStar_List_Tot_Base.length
                                                                    bs2) ss)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun v1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    (Pulse_Syntax_Naming.shift_subst_n
                                                                    (FStar_List_Tot_Base.length
                                                                    bs2) ss)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (open_binders
                                                                    g bs2
                                                                    (Pulse_Typing_Env.push_binding
                                                                    uvs x
                                                                    b.Pulse_Syntax_Base.binder_ppname
                                                                    b.Pulse_Syntax_Base.binder_ty)
                                                                    v1 body1))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                              uu___1)))
                                                   uu___1))) uu___)))) uu___4
              uu___3 uu___2 uu___1 uu___
let (closing :
  (Pulse_Syntax_Base.ppname * Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ)
    Prims.list -> Pulse_Syntax_Naming.subst)
  =
  fun bs ->
    FStar_Pervasives_Native.snd
      (FStar_List_Tot_Base.fold_right
         (fun uu___ ->
            fun uu___1 ->
              match (uu___, uu___1) with
              | ((uu___2, x, uu___3), (n, ss)) ->
                  ((n + Prims.int_one), ((Pulse_Syntax_Naming.ND (x, n)) ::
                    ss))) bs (Prims.int_zero, []))
let rec (close_binders :
  (Pulse_Syntax_Base.ppname * Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ)
    Prims.list -> Pulse_Syntax_Base.binder Prims.list)
  =
  fun bs ->
    match bs with
    | [] -> []
    | (name, x, t)::bs1 ->
        let bss =
          FStar_List_Tot_Base.mapi
            (fun n ->
               fun uu___ ->
                 match uu___ with
                 | (n1, x1, t1) ->
                     (n1, x1,
                       (Pulse_Syntax_Naming.subst_term t1
                          [Pulse_Syntax_Naming.ND (x, n)]))) bs1 in
        let b = Pulse_Syntax_Base.mk_binder_ppname t name in b ::
          (close_binders bss)
let (unfold_defs :
  Pulse_Typing_Env.env ->
    Prims.string Prims.list FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun defs ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (128)) (Prims.of_int (12))
                   (Prims.of_int (128)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (128)) (Prims.of_int (26))
                   (Prims.of_int (149)) (Prims.of_int (89)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Elaborate_Pure.elab_term t))
          (fun uu___ ->
             (fun t1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.AssertWithBinders.fst"
                              (Prims.of_int (129)) (Prims.of_int (18))
                              (Prims.of_int (129)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.AssertWithBinders.fst"
                              (Prims.of_int (128)) (Prims.of_int (26))
                              (Prims.of_int (149)) (Prims.of_int (89)))))
                     (Obj.magic
                        (FStar_Tactics_V2_SyntaxHelpers.collect_app t1))
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
                                                  (Prims.of_int (133))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (133))
                                                  (Prims.of_int (54)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                  (Prims.of_int (133))
                                                  (Prims.of_int (57))
                                                  (Prims.of_int (145))
                                                  (Prims.of_int (10)))))
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               FStar_String.concat "."
                                                 (FStar_Reflection_V2_Builtins.inspect_fv
                                                    fv)))
                                         (fun uu___2 ->
                                            (fun head1 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.AssertWithBinders.fst"
                                                             (Prims.of_int (135))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (137))
                                                             (Prims.of_int (22)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.AssertWithBinders.fst"
                                                             (Prims.of_int (138))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (145))
                                                             (Prims.of_int (10)))))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          match defs with
                                                          | FStar_Pervasives_Native.Some
                                                              defs1 -> defs1
                                                          | FStar_Pervasives_Native.None
                                                              -> []))
                                                    (fun uu___2 ->
                                                       (fun fully ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (57)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (10)))))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___2
                                                                    ->
                                                                    Pulse_RuntimeUtils.unfold_def
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g) head1
                                                                    fully t1))
                                                               (fun uu___2 ->
                                                                  (fun rt ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (75)))))
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
                                                                    t1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "unfolding "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " returned None")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (option_must
                                                                    rt uu___2))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun rt1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (93)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (92)))))
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
                                                                    rt1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "error in reading back the unfolded term "
                                                                    (Prims.strcat
                                                                    uu___2 "")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (option_must
                                                                    (Pulse_Readback.readback_ty
                                                                    rt1)
                                                                    uu___2))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (142))
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
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
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
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (134)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    rt1))
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
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (112)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    t1))
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
                                                                    uu___2)))
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
                                                  (Prims.of_int (133))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (133))
                                                  (Prims.of_int (54)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                  (Prims.of_int (133))
                                                  (Prims.of_int (57))
                                                  (Prims.of_int (145))
                                                  (Prims.of_int (10)))))
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___3 ->
                                               FStar_String.concat "."
                                                 (FStar_Reflection_V2_Builtins.inspect_fv
                                                    fv)))
                                         (fun uu___3 ->
                                            (fun head1 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.AssertWithBinders.fst"
                                                             (Prims.of_int (135))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (137))
                                                             (Prims.of_int (22)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.AssertWithBinders.fst"
                                                             (Prims.of_int (138))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (145))
                                                             (Prims.of_int (10)))))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          match defs with
                                                          | FStar_Pervasives_Native.Some
                                                              defs1 -> defs1
                                                          | FStar_Pervasives_Native.None
                                                              -> []))
                                                    (fun uu___3 ->
                                                       (fun fully ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (57)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (10)))))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___3
                                                                    ->
                                                                    Pulse_RuntimeUtils.unfold_def
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g) head1
                                                                    fully t1))
                                                               (fun uu___3 ->
                                                                  (fun rt ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (75)))))
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
                                                                    t1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "unfolding "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " returned None")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (option_must
                                                                    rt uu___3))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun rt1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (93)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (92)))))
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
                                                                    rt1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "error in reading back the unfolded term "
                                                                    (Prims.strcat
                                                                    uu___3 "")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (option_must
                                                                    (Pulse_Readback.readback_ty
                                                                    rt1)
                                                                    uu___3))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (142))
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
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
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
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (134)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    rt1))
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
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (112)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    t1))
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
                                                                    uu___3)))
                                                                    uu___3)))
                                                         uu___3))) uu___3))
                                | uu___2 ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                  (Prims.of_int (149))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (149))
                                                  (Prims.of_int (89)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                  (Prims.of_int (148))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (149))
                                                  (Prims.of_int (89)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.AssertWithBinders.fst"
                                                        (Prims.of_int (149))
                                                        (Prims.of_int (68))
                                                        (Prims.of_int (149))
                                                        (Prims.of_int (88)))))
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
                                                     t1))
                                               (fun uu___3 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___4 ->
                                                       Prims.strcat
                                                         "Cannot unfold "
                                                         (Prims.strcat uu___3
                                                            ", the head is not an fvar")))))
                                         (fun uu___3 ->
                                            (fun uu___3 ->
                                               Obj.magic
                                                 (Pulse_Typing_Env.fail g
                                                    (FStar_Pervasives_Native.Some
                                                       (Pulse_RuntimeUtils.range_of_term
                                                          t1)) uu___3))
                                              uu___3)))) uu___))) uu___)
let (check_unfoldable :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun v ->
           match v.Pulse_Syntax_Base.t with
           | Pulse_Syntax_Base.Tm_FStar uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ())))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (157)) (Prims.of_int (6))
                                (Prims.of_int (159)) (Prims.of_int (45)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (155)) (Prims.of_int (3))
                                (Prims.of_int (159)) (Prims.of_int (45)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.AssertWithBinders.fst"
                                      (Prims.of_int (159))
                                      (Prims.of_int (24))
                                      (Prims.of_int (159))
                                      (Prims.of_int (44)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "prims.fst"
                                      (Prims.of_int (590))
                                      (Prims.of_int (19))
                                      (Prims.of_int (590))
                                      (Prims.of_int (31)))))
                             (Obj.magic
                                (Pulse_Syntax_Printer.term_to_string v))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     Prims.strcat
                                       "`fold` and `unfold` expect a single user-defined predicate as an argument, but "
                                       (Prims.strcat uu___1
                                          " is a primitive term that cannot be folded or unfolded")))))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (Pulse_Typing_Env.fail g
                                  (FStar_Pervasives_Native.Some
                                     (v.Pulse_Syntax_Base.range1)) uu___1))
                            uu___1)))) uu___1 uu___
let (visit_and_rewrite :
  (FStar_Reflection_Types.term * FStar_Reflection_Types.term) ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                 (Prims.of_int (163)) (Prims.of_int (17))
                 (Prims.of_int (163)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                 (Prims.of_int (162)) (Prims.of_int (40))
                 (Prims.of_int (195)) (Prims.of_int (9)))))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> p))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (lhs, rhs) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (165)) (Prims.of_int (4))
                                (Prims.of_int (165)) (Prims.of_int (36)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (167)) (Prims.of_int (2))
                                (Prims.of_int (195)) (Prims.of_int (9)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             fun uu___1 ->
                               (fun uu___1 ->
                                  fun t1 ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            if
                                              FStar_Reflection_V2_TermEq.term_eq
                                                t1 lhs
                                            then rhs
                                            else t1))) uu___2 uu___1))
                       (fun uu___1 ->
                          (fun visitor ->
                             match FStar_Reflection_V2_Builtins.inspect_ln
                                     lhs
                             with
                             | FStar_Reflection_V2_Data.Tv_Var n ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            Pulse_Syntax_Naming.subst_term t
                                              [Pulse_Syntax_Naming.NT
                                                 (((FStar_Reflection_V2_Builtins.inspect_namedv
                                                      n).FStar_Reflection_V2_Data.uniq),
                                                   {
                                                     Pulse_Syntax_Base.t =
                                                       (Pulse_Syntax_Base.Tm_FStar
                                                          rhs);
                                                     Pulse_Syntax_Base.range1
                                                       =
                                                       (t.Pulse_Syntax_Base.range1)
                                                   })])))
                             | uu___1 ->
                                 Obj.magic
                                   (Obj.repr
                                      (let rec aux uu___2 =
                                         (fun t1 ->
                                            match t1.Pulse_Syntax_Base.t with
                                            | Pulse_Syntax_Base.Tm_Emp ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 -> t1)))
                                            | Pulse_Syntax_Base.Tm_VProp ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 -> t1)))
                                            | Pulse_Syntax_Base.Tm_Inames ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 -> t1)))
                                            | Pulse_Syntax_Base.Tm_EmpInames
                                                ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 -> t1)))
                                            | Pulse_Syntax_Base.Tm_Inames ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 -> t1)))
                                            | Pulse_Syntax_Base.Tm_Unknown ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 -> t1)))
                                            | Pulse_Syntax_Base.Tm_Inv i ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (183))
                                                                 (Prims.of_int (21))
                                                                 (Prims.of_int (183))
                                                                 (Prims.of_int (35)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (183))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (183))
                                                                 (Prims.of_int (35)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (35)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (35)))))
                                                              (Obj.magic
                                                                 (aux i))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Base.Tm_Inv
                                                                    uu___2))))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                {
                                                                  Pulse_Syntax_Base.t
                                                                    = uu___2;
                                                                  Pulse_Syntax_Base.range1
                                                                    =
                                                                    (
                                                                    t1.Pulse_Syntax_Base.range1)
                                                                }))))
                                            | Pulse_Syntax_Base.Tm_AddInv
                                                (i, is) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (185))
                                                                 (Prims.of_int (21))
                                                                 (Prims.of_int (185))
                                                                 (Prims.of_int (47)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (185))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (185))
                                                                 (Prims.of_int (47)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (38)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (47)))))
                                                              (Obj.magic
                                                                 (aux i))
                                                              (fun uu___2 ->
                                                                 (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (aux is))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.Tm_AddInv
                                                                    (uu___2,
                                                                    uu___3)))))
                                                                   uu___2)))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                {
                                                                  Pulse_Syntax_Base.t
                                                                    = uu___2;
                                                                  Pulse_Syntax_Base.range1
                                                                    =
                                                                    (
                                                                    t1.Pulse_Syntax_Base.range1)
                                                                }))))
                                            | Pulse_Syntax_Base.Tm_Pure p1 ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (186))
                                                                 (Prims.of_int (34))
                                                                 (Prims.of_int (186))
                                                                 (Prims.of_int (49)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (186))
                                                                 (Prims.of_int (23))
                                                                 (Prims.of_int (186))
                                                                 (Prims.of_int (49)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (49)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (49)))))
                                                              (Obj.magic
                                                                 (aux p1))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    uu___2))))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                {
                                                                  Pulse_Syntax_Base.t
                                                                    = uu___2;
                                                                  Pulse_Syntax_Base.range1
                                                                    =
                                                                    (
                                                                    t1.Pulse_Syntax_Base.range1)
                                                                }))))
                                            | Pulse_Syntax_Base.Tm_Star
                                                (l, r) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (187))
                                                                 (Prims.of_int (37))
                                                                 (Prims.of_int (187))
                                                                 (Prims.of_int (60)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (187))
                                                                 (Prims.of_int (26))
                                                                 (Prims.of_int (187))
                                                                 (Prims.of_int (60)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (52)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (60)))))
                                                              (Obj.magic
                                                                 (aux l))
                                                              (fun uu___2 ->
                                                                 (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (aux r))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.Tm_Star
                                                                    (uu___2,
                                                                    uu___3)))))
                                                                   uu___2)))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                {
                                                                  Pulse_Syntax_Base.t
                                                                    = uu___2;
                                                                  Pulse_Syntax_Base.range1
                                                                    =
                                                                    (
                                                                    t1.Pulse_Syntax_Base.range1)
                                                                }))))
                                            | Pulse_Syntax_Base.Tm_ExistsSL
                                                (u, b, body) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (188))
                                                                 (Prims.of_int (45))
                                                                 (Prims.of_int (188))
                                                                 (Prims.of_int (105)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (188))
                                                                 (Prims.of_int (34))
                                                                 (Prims.of_int (188))
                                                                 (Prims.of_int (105)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (93)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (105)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (93)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (93)))))
                                                                    (
                                                                    Obj.magic
                                                                    (aux
                                                                    b.Pulse_Syntax_Base.binder_ty))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = uu___2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    =
                                                                    (b.Pulse_Syntax_Base.binder_ppname);
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    (b.Pulse_Syntax_Base.binder_attrs)
                                                                    }))))
                                                              (fun uu___2 ->
                                                                 (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    (aux body))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u,
                                                                    uu___2,
                                                                    uu___3)))))
                                                                   uu___2)))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                {
                                                                  Pulse_Syntax_Base.t
                                                                    = uu___2;
                                                                  Pulse_Syntax_Base.range1
                                                                    =
                                                                    (
                                                                    t1.Pulse_Syntax_Base.range1)
                                                                }))))
                                            | Pulse_Syntax_Base.Tm_ForallSL
                                                (u, b, body) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (189))
                                                                 (Prims.of_int (45))
                                                                 (Prims.of_int (189))
                                                                 (Prims.of_int (105)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (189))
                                                                 (Prims.of_int (34))
                                                                 (Prims.of_int (189))
                                                                 (Prims.of_int (105)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (93)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (105)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (93)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (93)))))
                                                                    (
                                                                    Obj.magic
                                                                    (aux
                                                                    b.Pulse_Syntax_Base.binder_ty))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = uu___2;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    =
                                                                    (b.Pulse_Syntax_Base.binder_ppname);
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    (b.Pulse_Syntax_Base.binder_attrs)
                                                                    }))))
                                                              (fun uu___2 ->
                                                                 (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    (aux body))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.Tm_ForallSL
                                                                    (u,
                                                                    uu___2,
                                                                    uu___3)))))
                                                                   uu___2)))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                {
                                                                  Pulse_Syntax_Base.t
                                                                    = uu___2;
                                                                  Pulse_Syntax_Base.range1
                                                                    =
                                                                    (
                                                                    t1.Pulse_Syntax_Base.range1)
                                                                }))))
                                            | Pulse_Syntax_Base.Tm_FStar h ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (191))
                                                                 (Prims.of_int (16))
                                                                 (Prims.of_int (191))
                                                                 (Prims.of_int (54)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (193))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (193))
                                                                 (Prims.of_int (29)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Visit.visit_tm
                                                              visitor h))
                                                        (fun h1 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                {
                                                                  Pulse_Syntax_Base.t
                                                                    =
                                                                    (
                                                                    Pulse_Syntax_Base.Tm_FStar
                                                                    h1);
                                                                  Pulse_Syntax_Base.range1
                                                                    =
                                                                    (
                                                                    t1.Pulse_Syntax_Base.range1)
                                                                }))))) uu___2 in
                                       aux t))) uu___1))) uu___)
let (visit_and_rewrite_conjuncts :
  (FStar_Reflection_Types.term * FStar_Reflection_Types.term) ->
    Pulse_Syntax_Base.term Prims.list ->
      (Pulse_Syntax_Base.term Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  = fun p -> fun tms -> FStar_Tactics_Util.map (visit_and_rewrite p) tms
let (visit_and_rewrite_conjuncts_all :
  (FStar_Reflection_Types.term * FStar_Reflection_Types.term) Prims.list ->
    Pulse_Syntax_Base.term ->
      ((Pulse_Syntax_Base.term * Pulse_Syntax_Base.term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    fun goal ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                 (Prims.of_int (201)) (Prims.of_int (12))
                 (Prims.of_int (201)) (Prims.of_int (55)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                 (Prims.of_int (201)) (Prims.of_int (58))
                 (Prims.of_int (213)) (Prims.of_int (44)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing_Combinators.vprop_as_list goal))
        (fun uu___ ->
           (fun tms ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.AssertWithBinders.fst"
                            (Prims.of_int (202)) (Prims.of_int (13))
                            (Prims.of_int (202)) (Prims.of_int (79)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.AssertWithBinders.fst"
                            (Prims.of_int (203)) (Prims.of_int (41))
                            (Prims.of_int (213)) (Prims.of_int (44)))))
                   (Obj.magic
                      (FStar_Tactics_Util.fold_left
                         (fun tms1 ->
                            fun p1 -> visit_and_rewrite_conjuncts p1 tms1)
                         tms p))
                   (fun uu___ ->
                      (fun tms' ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.AssertWithBinders.fst"
                                       (Prims.of_int (205))
                                       (Prims.of_int (4))
                                       (Prims.of_int (210))
                                       (Prims.of_int (14)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.AssertWithBinders.fst"
                                       (Prims.of_int (203))
                                       (Prims.of_int (41))
                                       (Prims.of_int (213))
                                       (Prims.of_int (44)))))
                              (Obj.magic
                                 (FStar_Tactics_Util.fold_left2
                                    (fun uu___2 ->
                                       fun uu___1 ->
                                         fun uu___ ->
                                           (fun uu___ ->
                                              fun t ->
                                                fun t' ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          match uu___ with
                                                          | (lhs, rhs) ->
                                                              if
                                                                Pulse_Syntax_Base.eq_tm
                                                                  t t'
                                                              then (lhs, rhs)
                                                              else
                                                                ((t :: lhs),
                                                                  (t' ::
                                                                  rhs)))))
                                             uu___2 uu___1 uu___) ([], [])
                                    tms tms'))
                              (fun uu___ ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      match uu___ with
                                      | (lhs, rhs) ->
                                          ((Pulse_Typing_Combinators.list_as_vprop
                                              lhs),
                                            (Pulse_Typing_Combinators.list_as_vprop
                                               rhs)))))) uu___))) uu___)
let (disjoint :
  Pulse_Syntax_Base.var Prims.list ->
    Pulse_Syntax_Base.var FStar_Set.set -> Prims.bool)
  =
  fun dom ->
    fun cod ->
      FStar_List_Tot_Base.for_all
        (fun d -> Prims.op_Negation (FStar_Set.mem d cod)) dom
let rec (as_subst :
  (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list ->
    Pulse_Syntax_Naming.subst_elt Prims.list ->
      Pulse_Syntax_Base.var Prims.list ->
        Pulse_Syntax_Base.var FStar_Set.set ->
          Pulse_Syntax_Naming.subst_elt Prims.list
            FStar_Pervasives_Native.option)
  =
  fun p ->
    fun out ->
      fun domain ->
        fun codomain ->
          match p with
          | [] ->
              if disjoint domain codomain
              then FStar_Pervasives_Native.Some out
              else FStar_Pervasives_Native.None
          | (e1, e2)::p1 ->
              (match e1.Pulse_Syntax_Base.t with
               | Pulse_Syntax_Base.Tm_FStar e11 ->
                   (match FStar_Reflection_V2_Builtins.inspect_ln e11 with
                    | FStar_Reflection_V2_Data.Tv_Var n ->
                        let nv =
                          FStar_Reflection_V2_Builtins.inspect_namedv n in
                        as_subst p1
                          ((Pulse_Syntax_Naming.NT
                              ((nv.FStar_Reflection_V2_Data.uniq), e2)) ::
                          out) ((nv.FStar_Reflection_V2_Data.uniq) :: domain)
                          (FStar_Set.union codomain
                             (Pulse_Syntax_Naming.freevars e2))
                    | uu___ -> FStar_Pervasives_Native.None)
               | uu___ -> FStar_Pervasives_Native.None)
let (rewrite_all :
  Pulse_Typing_Env.env ->
    (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list ->
      Pulse_Syntax_Base.term ->
        ((Pulse_Syntax_Base.term * Pulse_Syntax_Base.term), unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun p ->
             fun t ->
               match as_subst p [] [] (FStar_Set.empty ()) with
               | FStar_Pervasives_Native.Some s ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              (t, (Pulse_Syntax_Naming.subst_term t s)))))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.AssertWithBinders.fst"
                                    (Prims.of_int (252)) (Prims.of_int (6))
                                    (Prims.of_int (256)) (Prims.of_int (9)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.AssertWithBinders.fst"
                                    (Prims.of_int (257)) (Prims.of_int (6))
                                    (Prims.of_int (260)) (Prims.of_int (12)))))
                           (Obj.magic
                              (FStar_Tactics_Util.map
                                 (fun uu___1 ->
                                    match uu___1 with
                                    | (e1, e2) ->
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.AssertWithBinders.fst"
                                                   (Prims.of_int (254))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (254))
                                                   (Prims.of_int (78)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.AssertWithBinders.fst"
                                                   (Prims.of_int (254))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (255))
                                                   (Prims.of_int (78)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.AssertWithBinders.fst"
                                                         (Prims.of_int (254))
                                                         (Prims.of_int (20))
                                                         (Prims.of_int (254))
                                                         (Prims.of_int (78)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.AssertWithBinders.fst"
                                                         (Prims.of_int (254))
                                                         (Prims.of_int (10))
                                                         (Prims.of_int (254))
                                                         (Prims.of_int (78)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (254))
                                                               (Prims.of_int (25))
                                                               (Prims.of_int (254))
                                                               (Prims.of_int (77)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (254))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (254))
                                                               (Prims.of_int (78)))))
                                                      (Obj.magic
                                                         (Pulse_Checker_Pure.instantiate_term_implicits
                                                            g e1))
                                                      (fun uu___2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 ->
                                                              FStar_Pervasives_Native.fst
                                                                uu___2))))
                                                (fun uu___2 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        Pulse_Elaborate_Pure.elab_term
                                                          uu___2))))
                                          (fun uu___2 ->
                                             (fun uu___2 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.AssertWithBinders.fst"
                                                              (Prims.of_int (255))
                                                              (Prims.of_int (10))
                                                              (Prims.of_int (255))
                                                              (Prims.of_int (78)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.AssertWithBinders.fst"
                                                              (Prims.of_int (254))
                                                              (Prims.of_int (10))
                                                              (Prims.of_int (255))
                                                              (Prims.of_int (78)))))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (78)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (78)))))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (77)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (78)))))
                                                                 (Obj.magic
                                                                    (
                                                                    Pulse_Checker_Pure.instantiate_term_implicits
                                                                    g e2))
                                                                 (fun uu___3
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___3))))
                                                           (fun uu___3 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   Pulse_Elaborate_Pure.elab_term
                                                                    uu___3))))
                                                     (fun uu___3 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             (uu___2, uu___3)))))
                                               uu___2)) p))
                           (fun uu___1 ->
                              (fun p1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (258))
                                               (Prims.of_int (19))
                                               (Prims.of_int (258))
                                               (Prims.of_int (54)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (257))
                                               (Prims.of_int (6))
                                               (Prims.of_int (260))
                                               (Prims.of_int (12)))))
                                      (Obj.magic
                                         (visit_and_rewrite_conjuncts_all p1
                                            t))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            match uu___1 with
                                            | (lhs, rhs) ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.AssertWithBinders.fst"
                                                              (Prims.of_int (259))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (259))
                                                              (Prims.of_int (106)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.AssertWithBinders.fst"
                                                              (Prims.of_int (260))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (260))
                                                              (Prims.of_int (12)))))
                                                     (Obj.magic
                                                        (debug_log g
                                                           (fun uu___2 ->
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (105)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (105)))))
                                                                (Obj.magic
                                                                   (Pulse_Syntax_Printer.term_to_string
                                                                    rhs))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    lhs))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Rewrote "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " to "))
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
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             (lhs, rhs)))))
                                           uu___1))) uu___1)))) uu___2 uu___1
          uu___
let (check_renaming :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun st ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (271)) (Prims.of_int (35))
                   (Prims.of_int (271)) (Prims.of_int (42)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (271)) Prims.int_one (Prims.of_int (297))
                   (Prims.of_int (3)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> st.Pulse_Syntax_Base.term1))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | Pulse_Syntax_Base.Tm_ProofHintWithBinders ht ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.AssertWithBinders.fst"
                                  (Prims.of_int (272)) (Prims.of_int (65))
                                  (Prims.of_int (272)) (Prims.of_int (67)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.AssertWithBinders.fst"
                                  (Prims.of_int (271)) (Prims.of_int (45))
                                  (Prims.of_int (297)) (Prims.of_int (3)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> ht))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               match uu___1 with
                               | {
                                   Pulse_Syntax_Base.hint_type =
                                     Pulse_Syntax_Base.RENAME
                                     { Pulse_Syntax_Base.pairs = pairs;
                                       Pulse_Syntax_Base.goal = goal;_};
                                   Pulse_Syntax_Base.binders = bs;
                                   Pulse_Syntax_Base.t3 = body;_} ->
                                   (match (bs, goal) with
                                    | (uu___2::uu___3,
                                       FStar_Pervasives_Native.None) ->
                                        Obj.magic
                                          (Obj.repr
                                             (Pulse_Typing_Env.fail g
                                                (FStar_Pervasives_Native.Some
                                                   (st.Pulse_Syntax_Base.range2))
                                                "A renaming with binders must have a goal (with xs. rename ... in goal)"))
                                    | (uu___2::uu___3,
                                       FStar_Pervasives_Native.Some goal1) ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___4 ->
                                                   {
                                                     Pulse_Syntax_Base.term1
                                                       =
                                                       (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                          {
                                                            Pulse_Syntax_Base.hint_type
                                                              =
                                                              (Pulse_Syntax_Base.ASSERT
                                                                 {
                                                                   Pulse_Syntax_Base.p
                                                                    = goal1
                                                                 });
                                                            Pulse_Syntax_Base.binders
                                                              = bs;
                                                            Pulse_Syntax_Base.t3
                                                              =
                                                              {
                                                                Pulse_Syntax_Base.term1
                                                                  =
                                                                  (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    {
                                                                    Pulse_Syntax_Base.hint_type
                                                                    =
                                                                    (ht.Pulse_Syntax_Base.hint_type);
                                                                    Pulse_Syntax_Base.binders
                                                                    = [];
                                                                    Pulse_Syntax_Base.t3
                                                                    =
                                                                    (ht.Pulse_Syntax_Base.t3)
                                                                    });
                                                                Pulse_Syntax_Base.range2
                                                                  =
                                                                  (st.Pulse_Syntax_Base.range2);
                                                                Pulse_Syntax_Base.effect_tag
                                                                  =
                                                                  (st.Pulse_Syntax_Base.effect_tag)
                                                              }
                                                          });
                                                     Pulse_Syntax_Base.range2
                                                       =
                                                       (st.Pulse_Syntax_Base.range2);
                                                     Pulse_Syntax_Base.effect_tag
                                                       =
                                                       (st.Pulse_Syntax_Base.effect_tag)
                                                   })))
                                    | ([], FStar_Pervasives_Native.None) ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.AssertWithBinders.fst"
                                                         (Prims.of_int (288))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (288))
                                                         (Prims.of_int (42)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.AssertWithBinders.fst"
                                                         (Prims.of_int (286))
                                                         (Prims.of_int (15))
                                                         (Prims.of_int (290))
                                                         (Prims.of_int (77)))))
                                                (Obj.magic
                                                   (rewrite_all g pairs pre))
                                                (fun uu___2 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        match uu___2 with
                                                        | (lhs, rhs) ->
                                                            {
                                                              Pulse_Syntax_Base.term1
                                                                =
                                                                (Pulse_Syntax_Base.Tm_Bind
                                                                   {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    (Pulse_Syntax_Base.as_binder
                                                                    Pulse_Typing.tm_unit);
                                                                    Pulse_Syntax_Base.head1
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t11
                                                                    = lhs;
                                                                    Pulse_Syntax_Base.t21
                                                                    = rhs
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st.Pulse_Syntax_Base.effect_tag)
                                                                    };
                                                                    Pulse_Syntax_Base.body1
                                                                    = body
                                                                   });
                                                              Pulse_Syntax_Base.range2
                                                                =
                                                                (st.Pulse_Syntax_Base.range2);
                                                              Pulse_Syntax_Base.effect_tag
                                                                =
                                                                (st.Pulse_Syntax_Base.effect_tag)
                                                            }))))
                                    | ([], FStar_Pervasives_Native.Some
                                       goal1) ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.AssertWithBinders.fst"
                                                         (Prims.of_int (293))
                                                         (Prims.of_int (20))
                                                         (Prims.of_int (293))
                                                         (Prims.of_int (56)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.AssertWithBinders.fst"
                                                         (Prims.of_int (292))
                                                         (Prims.of_int (21))
                                                         (Prims.of_int (297))
                                                         (Prims.of_int (3)))))
                                                (Obj.magic
                                                   (Pulse_Checker_Pure.instantiate_term_implicits
                                                      g goal1))
                                                (fun uu___2 ->
                                                   (fun uu___2 ->
                                                      match uu___2 with
                                                      | (goal2, uu___3) ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (45)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (79)))))
                                                               (Obj.magic
                                                                  (rewrite_all
                                                                    g pairs
                                                                    goal2))
                                                               (fun uu___4 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (lhs,
                                                                    rhs) ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    (Pulse_Syntax_Base.as_binder
                                                                    Pulse_Typing.tm_unit);
                                                                    Pulse_Syntax_Base.head1
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t11
                                                                    = lhs;
                                                                    Pulse_Syntax_Base.t21
                                                                    = rhs
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st.Pulse_Syntax_Base.effect_tag)
                                                                    };
                                                                    Pulse_Syntax_Base.body1
                                                                    = body
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st.Pulse_Syntax_Base.effect_tag)
                                                                    }))))
                                                     uu___2))))) uu___1)))
               uu___)
let (check_wild :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun st ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (304)) (Prims.of_int (35))
                   (Prims.of_int (304)) (Prims.of_int (42)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (304)) Prims.int_one (Prims.of_int (334))
                   (Prims.of_int (23)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> st.Pulse_Syntax_Base.term1))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | Pulse_Syntax_Base.Tm_ProofHintWithBinders ht ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.AssertWithBinders.fst"
                                  (Prims.of_int (305)) (Prims.of_int (31))
                                  (Prims.of_int (305)) (Prims.of_int (33)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.AssertWithBinders.fst"
                                  (Prims.of_int (304)) (Prims.of_int (45))
                                  (Prims.of_int (334)) (Prims.of_int (23)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> ht))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               match uu___1 with
                               | { Pulse_Syntax_Base.hint_type = uu___2;
                                   Pulse_Syntax_Base.binders = bs;
                                   Pulse_Syntax_Base.t3 = body;_} ->
                                   (match bs with
                                    | [] ->
                                        Obj.magic
                                          (Pulse_Typing_Env.fail g
                                             (FStar_Pervasives_Native.Some
                                                (st.Pulse_Syntax_Base.range2))
                                             "A wildcard must have at least one binder")
                                    | uu___3 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.AssertWithBinders.fst"
                                                      (Prims.of_int (311))
                                                      (Prims.of_int (17))
                                                      (Prims.of_int (311))
                                                      (Prims.of_int (59)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.AssertWithBinders.fst"
                                                      (Prims.of_int (311))
                                                      (Prims.of_int (62))
                                                      (Prims.of_int (334))
                                                      (Prims.of_int (23)))))
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___4 ->
                                                   Pulse_Typing_Combinators.vprop_as_list
                                                     pre))
                                             (fun uu___4 ->
                                                (fun vprops ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (312))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (312))
                                                                 (Prims.of_int (80)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (311))
                                                                 (Prims.of_int (62))
                                                                 (Prims.of_int (334))
                                                                 (Prims.of_int (23)))))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              FStar_List_Tot_Base.partition
                                                                (fun v ->
                                                                   Pulse_Syntax_Base.uu___is_Tm_ExistsSL
                                                                    v.Pulse_Syntax_Base.t)
                                                                vprops))
                                                        (fun uu___4 ->
                                                           (fun uu___4 ->
                                                              match uu___4
                                                              with
                                                              | (ex, rest) ->
                                                                  (match ex
                                                                   with
                                                                   | 
                                                                   [] ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.range2))
                                                                    "Binding names with a wildcard requires exactly one existential quantifier in the goal")
                                                                   | 
                                                                   uu___5::uu___6::uu___7
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.range2))
                                                                    "Binding names with a wildcard requires exactly one existential quantifier in the goal")
                                                                   | 
                                                                   ex1::[] ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_List_Tot_Base.length
                                                                    bs))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun k ->
                                                                    let rec peel_binders
                                                                    uu___6
                                                                    uu___5 =
                                                                    (fun n ->
                                                                    fun t ->
                                                                    if
                                                                    n =
                                                                    Prims.int_zero
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    {
                                                                    Pulse_Syntax_Base.hint_type
                                                                    =
                                                                    (Pulse_Syntax_Base.ASSERT
                                                                    {
                                                                    Pulse_Syntax_Base.p
                                                                    = t
                                                                    });
                                                                    Pulse_Syntax_Base.binders
                                                                    =
                                                                    (ht.Pulse_Syntax_Base.binders);
                                                                    Pulse_Syntax_Base.t3
                                                                    =
                                                                    (ht.Pulse_Syntax_Base.t3)
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st.Pulse_Syntax_Base.effect_tag)
                                                                    })))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    t.Pulse_Syntax_Base.t
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, b,
                                                                    body1) ->
                                                                    peel_binders
                                                                    (n -
                                                                    Prims.int_one)
                                                                    body1
                                                                    | 
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.uu___30
                                                                    ex1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Expected an existential quantifier with at least "
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    k)
                                                                    " binders; but only found "))
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    " with "))
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    x)
                                                                    " binders")))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    (k - n)))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.range2))
                                                                    uu___7))
                                                                    uu___7))))
                                                                    uu___6
                                                                    uu___5 in
                                                                    Obj.magic
                                                                    (peel_binders
                                                                    k ex1))
                                                                    uu___5))))
                                                             uu___4))) uu___4))))
                              uu___1))) uu___)
let rec (add_rem_uvs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.typ ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.vprop ->
          ((Pulse_Typing_Env.env, Pulse_Syntax_Base.vprop) Prims.dtuple2,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun t ->
               fun uvs ->
                 fun v ->
                   match Pulse_Syntax_Pure.is_arrow t with
                   | FStar_Pervasives_Native.None ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> Prims.Mkdtuple2 (uvs, v))))
                   | FStar_Pervasives_Native.Some (b, qopt, c) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.AssertWithBinders.fst"
                                        (Prims.of_int (345))
                                        (Prims.of_int (12))
                                        (Prims.of_int (345))
                                        (Prims.of_int (34)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.AssertWithBinders.fst"
                                        (Prims.of_int (345))
                                        (Prims.of_int (37))
                                        (Prims.of_int (349))
                                        (Prims.of_int (37)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___ ->
                                     Pulse_Typing_Env.fresh
                                       (Pulse_Typing_Env.push_env g uvs)))
                               (fun uu___ ->
                                  (fun x ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.AssertWithBinders.fst"
                                                   (Prims.of_int (346))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (346))
                                                   (Prims.of_int (48)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.AssertWithBinders.fst"
                                                   (Prims.of_int (346))
                                                   (Prims.of_int (51))
                                                   (Prims.of_int (349))
                                                   (Prims.of_int (37)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___ ->
                                                Pulse_Syntax_Naming.open_comp_nv
                                                  c
                                                  ((b.Pulse_Syntax_Base.binder_ppname),
                                                    x)))
                                          (fun uu___ ->
                                             (fun ct ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.AssertWithBinders.fst"
                                                              (Prims.of_int (347))
                                                              (Prims.of_int (14))
                                                              (Prims.of_int (347))
                                                              (Prims.of_int (64)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.AssertWithBinders.fst"
                                                              (Prims.of_int (347))
                                                              (Prims.of_int (67))
                                                              (Prims.of_int (349))
                                                              (Prims.of_int (37)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___ ->
                                                           Pulse_Typing_Env.push_binding
                                                             uvs x
                                                             b.Pulse_Syntax_Base.binder_ppname
                                                             b.Pulse_Syntax_Base.binder_ty))
                                                     (fun uu___ ->
                                                        (fun uvs1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (82)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (37)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun uu___
                                                                    ->
                                                                    Pulse_Syntax_Pure.tm_pureapp
                                                                    v qopt
                                                                    (Pulse_Syntax_Pure.tm_var
                                                                    {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    =
                                                                    (b.Pulse_Syntax_Base.binder_ppname)
                                                                    })))
                                                                (fun uu___ ->
                                                                   (fun v1 ->
                                                                    Obj.magic
                                                                    (add_rem_uvs
                                                                    g
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    ct) uvs1
                                                                    v1))
                                                                    uu___)))
                                                          uu___))) uu___)))
                                    uu___)))) uu___3 uu___2 uu___1 uu___
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
            fun st ->
              fun check1 ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.AssertWithBinders.fst"
                           (Prims.of_int (362)) (Prims.of_int (10))
                           (Prims.of_int (362)) (Prims.of_int (48)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.AssertWithBinders.fst"
                           (Prims.of_int (362)) (Prims.of_int (51))
                           (Prims.of_int (465)) (Prims.of_int (50)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Typing_Env.push_context g "check_assert"
                          st.Pulse_Syntax_Base.range2))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.AssertWithBinders.fst"
                                      (Prims.of_int (364))
                                      (Prims.of_int (66))
                                      (Prims.of_int (364))
                                      (Prims.of_int (73)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.AssertWithBinders.fst"
                                      (Prims.of_int (362))
                                      (Prims.of_int (51))
                                      (Prims.of_int (465))
                                      (Prims.of_int (50)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> st.Pulse_Syntax_Base.term1))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                       {
                                         Pulse_Syntax_Base.hint_type =
                                           hint_type;
                                         Pulse_Syntax_Base.binders = bs;
                                         Pulse_Syntax_Base.t3 = body;_}
                                       ->
                                       (match hint_type with
                                        | Pulse_Syntax_Base.WILD ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (368))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (368))
                                                          (Prims.of_int (32)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (369))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (369))
                                                          (Prims.of_int (50)))))
                                                 (Obj.magic
                                                    (check_wild g1 pre st))
                                                 (fun uu___1 ->
                                                    (fun st1 ->
                                                       Obj.magic
                                                         (check1 g1 pre ()
                                                            post_hint
                                                            res_ppname st1))
                                                      uu___1))
                                        | Pulse_Syntax_Base.SHOW_PROOF_STATE
                                            r ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (374))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (377))
                                                          (Prims.of_int (5)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (378))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (378))
                                                          (Prims.of_int (36)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (375))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (376))
                                                                (Prims.of_int (27)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (374))
                                                                (Prims.of_int (14))
                                                                (Prims.of_int (377))
                                                                (Prims.of_int (5)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (27)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (27)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (27)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (27)))))
                                                                   (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    pre))
                                                                   (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_PP.indent
                                                                    uu___1))))
                                                             (fun uu___1 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___2
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "Current context:")
                                                                    uu___1))))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               [uu___1]))))
                                                 (fun uu___1 ->
                                                    (fun msg ->
                                                       Obj.magic
                                                         (Pulse_Typing_Env.fail_doc_env
                                                            true g1
                                                            (FStar_Pervasives_Native.Some
                                                               r) msg))
                                                      uu___1))
                                        | Pulse_Syntax_Base.RENAME
                                            {
                                              Pulse_Syntax_Base.pairs = pairs;
                                              Pulse_Syntax_Base.goal = goal;_}
                                            ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (380))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (380))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (381))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (381))
                                                          (Prims.of_int (50)))))
                                                 (Obj.magic
                                                    (check_renaming g1 pre st))
                                                 (fun uu___1 ->
                                                    (fun st1 ->
                                                       Obj.magic
                                                         (check1 g1 pre ()
                                                            post_hint
                                                            res_ppname st1))
                                                      uu___1))
                                        | Pulse_Syntax_Base.REWRITE
                                            { Pulse_Syntax_Base.t1 = t1;
                                              Pulse_Syntax_Base.t2 = t2;_}
                                            ->
                                            (match bs with
                                             | [] ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (386))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (386))
                                                               (Prims.of_int (52)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (387))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (388))
                                                               (Prims.of_int (83)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___1 ->
                                                            {
                                                              Pulse_Syntax_Base.term1
                                                                =
                                                                (Pulse_Syntax_Base.Tm_Rewrite
                                                                   {
                                                                    Pulse_Syntax_Base.t11
                                                                    = t1;
                                                                    Pulse_Syntax_Base.t21
                                                                    = t2
                                                                   });
                                                              Pulse_Syntax_Base.range2
                                                                =
                                                                (st.Pulse_Syntax_Base.range2);
                                                              Pulse_Syntax_Base.effect_tag
                                                                =
                                                                (st.Pulse_Syntax_Base.effect_tag)
                                                            }))
                                                      (fun uu___1 ->
                                                         (fun t ->
                                                            Obj.magic
                                                              (check1 g1 pre
                                                                 () post_hint
                                                                 res_ppname
                                                                 {
                                                                   Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    (Pulse_Syntax_Base.as_binder
                                                                    Pulse_Typing.tm_unit);
                                                                    Pulse_Syntax_Base.head1
                                                                    = t;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body
                                                                    });
                                                                   Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2);
                                                                   Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st.Pulse_Syntax_Base.effect_tag)
                                                                 })) uu___1))
                                             | uu___1 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (390))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (390))
                                                               (Prims.of_int (52)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (390))
                                                               (Prims.of_int (57))
                                                               (Prims.of_int (393))
                                                               (Prims.of_int (52)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___2 ->
                                                            {
                                                              Pulse_Syntax_Base.term1
                                                                =
                                                                (Pulse_Syntax_Base.Tm_Rewrite
                                                                   {
                                                                    Pulse_Syntax_Base.t11
                                                                    = t1;
                                                                    Pulse_Syntax_Base.t21
                                                                    = t2
                                                                   });
                                                              Pulse_Syntax_Base.range2
                                                                =
                                                                (st.Pulse_Syntax_Base.range2);
                                                              Pulse_Syntax_Base.effect_tag
                                                                =
                                                                (st.Pulse_Syntax_Base.effect_tag)
                                                            }))
                                                      (fun uu___2 ->
                                                         (fun t ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (88)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52)))))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    (Pulse_Syntax_Base.as_binder
                                                                    Pulse_Typing.tm_unit);
                                                                    Pulse_Syntax_Base.head1
                                                                    = t;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (113)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    {
                                                                    Pulse_Syntax_Base.hint_type
                                                                    =
                                                                    (Pulse_Syntax_Base.ASSERT
                                                                    {
                                                                    Pulse_Syntax_Base.p
                                                                    = t1
                                                                    });
                                                                    Pulse_Syntax_Base.binders
                                                                    = bs;
                                                                    Pulse_Syntax_Base.t3
                                                                    = body1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun st1
                                                                    ->
                                                                    Obj.magic
                                                                    (check1
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    st1))
                                                                    uu___2)))
                                                                    uu___2)))
                                                           uu___2)))
                                        | Pulse_Syntax_Base.ASSERT
                                            { Pulse_Syntax_Base.p = v;_} ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (397))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (397))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (397))
                                                          (Prims.of_int (37))
                                                          (Prims.of_int (413))
                                                          (Prims.of_int (52)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_BreakVC.break_vc
                                                       ()))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (38)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (52)))))
                                                            (Obj.magic
                                                               (infer_binder_types
                                                                  g1 bs v))
                                                            (fun uu___2 ->
                                                               (fun bs1 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (90)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (open_binders
                                                                    g1 bs1
                                                                    (Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g1)) v
                                                                    body))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (uvs,
                                                                    v_opened,
                                                                    body_opened)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (v_opened,
                                                                    body_opened)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (v1,
                                                                    body1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop
                                                                    (Pulse_Typing_Env.push_env
                                                                    g1 uvs)
                                                                    v1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (v2, d)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover.prove
                                                                    g pre ()
                                                                    uvs v2 ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (g11,
                                                                    nts,
                                                                    uu___6,
                                                                    pre',
                                                                    k_frame)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (check1
                                                                    g11
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    (Pulse_Checker_Prover_Substs.nt_subst_term
                                                                    v2 nts)
                                                                    pre') ()
                                                                    post_hint
                                                                    res_ppname
                                                                    (Pulse_Checker_Prover_Substs.nt_subst_st_term
                                                                    body1 nts)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, x_ty,
                                                                    pre'',
                                                                    g2, k) ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, x_ty,
                                                                    pre'',
                                                                    g2,
                                                                    (Pulse_Checker_Base.k_elab_trans
                                                                    g g11
                                                                    x_ty pre
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Substs.nt_subst_term
                                                                    v2 nts)
                                                                    pre')
                                                                    (FStar_Pervasives.dfst
                                                                    g2)
                                                                    k_frame k))))))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                 uu___2)))
                                                      uu___1))
                                        | Pulse_Syntax_Base.UNFOLD
                                            {
                                              Pulse_Syntax_Base.names1 =
                                                names;
                                              Pulse_Syntax_Base.p2 = v;_}
                                            ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (419))
                                                          (Prims.of_int (42))
                                                          (Prims.of_int (421))
                                                          (Prims.of_int (53)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (417))
                                                          (Prims.of_int (26))
                                                          (Prims.of_int (465))
                                                          (Prims.of_int (50)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (420))
                                                                (Prims.of_int (15))
                                                                (Prims.of_int (420))
                                                                (Prims.of_int (40)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (421))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (421))
                                                                (Prims.of_int (53)))))
                                                       (Obj.magic
                                                          (infer_binder_types
                                                             g1 bs v))
                                                       (fun uu___1 ->
                                                          (fun bs1 ->
                                                             Obj.magic
                                                               (open_binders
                                                                  g1 bs1
                                                                  (Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g1)) v
                                                                  body))
                                                            uu___1)))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       match uu___1 with
                                                       | FStar_Pervasives.Mkdtuple3
                                                           (uvs, v_opened,
                                                            body_opened)
                                                           ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (24)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                (Obj.magic
                                                                   (check_unfoldable
                                                                    g1 v))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.instantiate_term_implicits
                                                                    (Pulse_Typing_Env.push_env
                                                                    g1 uvs)
                                                                    v_opened))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (v_opened1,
                                                                    t_rem) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (add_rem_uvs
                                                                    (Pulse_Typing_Env.push_env
                                                                    g1 uvs)
                                                                    t_rem
                                                                    (Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g1))
                                                                    v_opened1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (uvs_rem,
                                                                    v_opened2)
                                                                    ->
                                                                    ((Pulse_Typing_Env.push_env
                                                                    uvs
                                                                    uvs_rem),
                                                                    v_opened2)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (uvs1,
                                                                    v_opened2)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (match hint_type
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.UNFOLD
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (435))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (unfold_defs
                                                                    (Pulse_Typing_Env.push_env
                                                                    g1 uvs1)
                                                                    FStar_Pervasives_Native.None
                                                                    v_opened2))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (v_opened2,
                                                                    uu___6))))
                                                                    | 
                                                                    Pulse_Syntax_Base.FOLD
                                                                    {
                                                                    Pulse_Syntax_Base.names
                                                                    = ns;
                                                                    Pulse_Syntax_Base.p1
                                                                    = uu___5;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    (unfold_defs
                                                                    (Pulse_Typing_Env.push_env
                                                                    g1 uvs1)
                                                                    ns
                                                                    v_opened2))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (uu___6,
                                                                    v_opened2)))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (lhs,
                                                                    rhs) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Env.bindings_with_ppname
                                                                    uvs1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_List_Tot_Base.rev
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uvs_bs ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    closing
                                                                    uvs_bs))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uvs_closing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.subst_term
                                                                    lhs
                                                                    uvs_closing))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun lhs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.subst_term
                                                                    rhs
                                                                    uvs_closing))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun rhs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body_opened
                                                                    uvs_closing))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    close_binders
                                                                    uvs_bs))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun bs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t11
                                                                    = lhs1;
                                                                    Pulse_Syntax_Base.t21
                                                                    = rhs1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    Pulse_Syntax_Base.STT_Ghost)
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
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    (Pulse_Syntax_Base.as_binder
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
                                                                    = body1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (body1.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun st1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match bs1
                                                                    with
                                                                    | 
                                                                    [] -> st1
                                                                    | 
                                                                    uu___7 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    {
                                                                    Pulse_Syntax_Base.hint_type
                                                                    =
                                                                    (Pulse_Syntax_Base.ASSERT
                                                                    {
                                                                    Pulse_Syntax_Base.p
                                                                    = lhs1
                                                                    });
                                                                    Pulse_Syntax_Base.binders
                                                                    = bs1;
                                                                    Pulse_Syntax_Base.t3
                                                                    = st1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st1.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st1.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun st2
                                                                    ->
                                                                    Obj.magic
                                                                    (check1
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    st2))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                      uu___1))
                                        | Pulse_Syntax_Base.FOLD
                                            {
                                              Pulse_Syntax_Base.names = names;
                                              Pulse_Syntax_Base.p1 = v;_}
                                            ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (419))
                                                          (Prims.of_int (42))
                                                          (Prims.of_int (421))
                                                          (Prims.of_int (53)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (417))
                                                          (Prims.of_int (26))
                                                          (Prims.of_int (465))
                                                          (Prims.of_int (50)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (420))
                                                                (Prims.of_int (15))
                                                                (Prims.of_int (420))
                                                                (Prims.of_int (40)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (421))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (421))
                                                                (Prims.of_int (53)))))
                                                       (Obj.magic
                                                          (infer_binder_types
                                                             g1 bs v))
                                                       (fun uu___1 ->
                                                          (fun bs1 ->
                                                             Obj.magic
                                                               (open_binders
                                                                  g1 bs1
                                                                  (Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g1)) v
                                                                  body))
                                                            uu___1)))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       match uu___1 with
                                                       | FStar_Pervasives.Mkdtuple3
                                                           (uvs, v_opened,
                                                            body_opened)
                                                           ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (24)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                (Obj.magic
                                                                   (check_unfoldable
                                                                    g1 v))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.instantiate_term_implicits
                                                                    (Pulse_Typing_Env.push_env
                                                                    g1 uvs)
                                                                    v_opened))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (v_opened1,
                                                                    t_rem) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (add_rem_uvs
                                                                    (Pulse_Typing_Env.push_env
                                                                    g1 uvs)
                                                                    t_rem
                                                                    (Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g1))
                                                                    v_opened1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (uvs_rem,
                                                                    v_opened2)
                                                                    ->
                                                                    ((Pulse_Typing_Env.push_env
                                                                    uvs
                                                                    uvs_rem),
                                                                    v_opened2)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (uvs1,
                                                                    v_opened2)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (match hint_type
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.UNFOLD
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (435))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (unfold_defs
                                                                    (Pulse_Typing_Env.push_env
                                                                    g1 uvs1)
                                                                    FStar_Pervasives_Native.None
                                                                    v_opened2))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (v_opened2,
                                                                    uu___6))))
                                                                    | 
                                                                    Pulse_Syntax_Base.FOLD
                                                                    {
                                                                    Pulse_Syntax_Base.names
                                                                    = ns;
                                                                    Pulse_Syntax_Base.p1
                                                                    = uu___5;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    (unfold_defs
                                                                    (Pulse_Typing_Env.push_env
                                                                    g1 uvs1)
                                                                    ns
                                                                    v_opened2))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (uu___6,
                                                                    v_opened2)))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (lhs,
                                                                    rhs) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Env.bindings_with_ppname
                                                                    uvs1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_List_Tot_Base.rev
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uvs_bs ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    closing
                                                                    uvs_bs))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uvs_closing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.subst_term
                                                                    lhs
                                                                    uvs_closing))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun lhs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.subst_term
                                                                    rhs
                                                                    uvs_closing))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun rhs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body_opened
                                                                    uvs_closing))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    close_binders
                                                                    uvs_bs))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun bs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t11
                                                                    = lhs1;
                                                                    Pulse_Syntax_Base.t21
                                                                    = rhs1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    Pulse_Syntax_Base.STT_Ghost)
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
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    (Pulse_Syntax_Base.as_binder
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
                                                                    = body1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (body1.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun st1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match bs1
                                                                    with
                                                                    | 
                                                                    [] -> st1
                                                                    | 
                                                                    uu___7 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    {
                                                                    Pulse_Syntax_Base.hint_type
                                                                    =
                                                                    (Pulse_Syntax_Base.ASSERT
                                                                    {
                                                                    Pulse_Syntax_Base.p
                                                                    = lhs1
                                                                    });
                                                                    Pulse_Syntax_Base.binders
                                                                    = bs1;
                                                                    Pulse_Syntax_Base.t3
                                                                    = st1
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st1.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st1.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun st2
                                                                    ->
                                                                    Obj.magic
                                                                    (check1
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    st2))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                      uu___1)))) uu___)))
                       uu___)