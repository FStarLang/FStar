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
                                (Prims.of_int (77)) (Prims.of_int (25))
                                (Prims.of_int (77)) (Prims.of_int (43)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (76)) (Prims.of_int (20))
                                (Prims.of_int (80)) (Prims.of_int (87)))))
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
                                               (Prims.of_int (78))
                                               (Prims.of_int (15))
                                               (Prims.of_int (78))
                                               (Prims.of_int (96)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (79))
                                               (Prims.of_int (4))
                                               (Prims.of_int (80))
                                               (Prims.of_int (87)))))
                                      (Obj.magic
                                         (option_must
                                            (Pulse_Readback.readback_ty sort)
                                            "Failed to readback elaborated binder in peel_off"))
                                      (fun uu___3 ->
                                         (fun sort1 ->
                                            Obj.magic
                                              (refl_abs_binders body
                                                 ({
                                                    Pulse_Syntax_Base.binder_ty
                                                      = sort1;
                                                    Pulse_Syntax_Base.binder_ppname
                                                      =
                                                      (Pulse_Syntax_Base.mk_ppname
                                                         ppname
                                                         (Pulse_RuntimeUtils.range_of_term
                                                            t))
                                                  } :: acc))) uu___3))) uu___)))
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
                                    (Prims.of_int (88)) (Prims.of_int (13))
                                    (Prims.of_int (88)) (Prims.of_int (24)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.AssertWithBinders.fst"
                                    (Prims.of_int (89)) (Prims.of_int (4))
                                    (Prims.of_int (111)) (Prims.of_int (80)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> Pulse_Elaborate_Pure.elab_term v))
                           (fun uu___1 ->
                              (fun tv ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (89))
                                               (Prims.of_int (4))
                                               (Prims.of_int (90))
                                               (Prims.of_int (94)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (90))
                                               (Prims.of_int (95))
                                               (Prims.of_int (111))
                                               (Prims.of_int (80)))))
                                      (if Prims.op_Negation (is_host_term tv)
                                       then
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (90))
                                                          (Prims.of_int (31))
                                                          (Prims.of_int (90))
                                                          (Prims.of_int (94)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (90))
                                                          (Prims.of_int (9))
                                                          (Prims.of_int (90))
                                                          (Prims.of_int (94)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (90))
                                                                (Prims.of_int (73))
                                                                (Prims.of_int (90))
                                                                (Prims.of_int (93)))))
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
                                                             v))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               Prims.strcat
                                                                 "Cannot infer type of "
                                                                 (Prims.strcat
                                                                    uu___1 "")))))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       Obj.magic
                                                         (Pulse_Typing_Env.fail
                                                            g
                                                            (FStar_Pervasives_Native.Some
                                                               (v.Pulse_Syntax_Base.range1))
                                                            uu___1)) uu___1)))
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
                                                          (Prims.of_int (92))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (98))
                                                          (Prims.of_int (20)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (99))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (111))
                                                          (Prims.of_int (80)))))
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
                                                    (fun as_binder ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (10)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (80)))))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  FStar_List_Tot_Base.fold_right
                                                                    (
                                                                    fun b ->
                                                                    fun tv1
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Abs
                                                                    ((as_binder
                                                                    b), tv1)))
                                                                    bs tv))
                                                            (fun uu___2 ->
                                                               (fun
                                                                  abstraction
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.instantiate_term_implicits
                                                                    g
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
                                                                    "Impossible: Instantiated abstraction is not embedded F* term"))))
                                                                    uu___2)))
                                                                 uu___2)))
                                                      uu___2))) uu___1)))
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
                                            (Prims.of_int (120))
                                            (Prims.of_int (12))
                                            (Prims.of_int (120))
                                            (Prims.of_int (58)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.AssertWithBinders.fst"
                                            (Prims.of_int (120))
                                            (Prims.of_int (61))
                                            (Prims.of_int (128))
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
                                                       (Prims.of_int (121))
                                                       (Prims.of_int (12))
                                                       (Prims.of_int (121))
                                                       (Prims.of_int (34)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.AssertWithBinders.fst"
                                                       (Prims.of_int (121))
                                                       (Prims.of_int (37))
                                                       (Prims.of_int (128))
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
                                                                  (Prims.of_int (122))
                                                                  (Prims.of_int (13))
                                                                  (Prims.of_int (122))
                                                                  (Prims.of_int (69)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                                  (Prims.of_int (122))
                                                                  (Prims.of_int (72))
                                                                  (Prims.of_int (128))
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
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (45)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (128))
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
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (128))
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
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (128))
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
                   (Prims.of_int (137)) (Prims.of_int (12))
                   (Prims.of_int (137)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (137)) (Prims.of_int (26))
                   (Prims.of_int (155)) (Prims.of_int (97)))))
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
                              (Prims.of_int (138)) (Prims.of_int (18))
                              (Prims.of_int (138)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.AssertWithBinders.fst"
                              (Prims.of_int (137)) (Prims.of_int (26))
                              (Prims.of_int (155)) (Prims.of_int (97)))))
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
                                                  (Prims.of_int (142))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (142))
                                                  (Prims.of_int (54)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                  (Prims.of_int (142))
                                                  (Prims.of_int (57))
                                                  (Prims.of_int (152))
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
                                                             (Prims.of_int (144))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (146))
                                                             (Prims.of_int (22)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.AssertWithBinders.fst"
                                                             (Prims.of_int (147))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (152))
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
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (57)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (152))
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
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (option_must
                                                                    rt
                                                                    "Unexpected: reduction produced an ill-formed term"))
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
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (option_must
                                                                    (Pulse_Readback.readback_ty
                                                                    rt1)
                                                                    "Unexpected: unable to readback unfolded term"))
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
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (150))
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
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
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
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (134)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
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
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (151))
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
                                                  (Prims.of_int (142))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (142))
                                                  (Prims.of_int (54)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                  (Prims.of_int (142))
                                                  (Prims.of_int (57))
                                                  (Prims.of_int (152))
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
                                                             (Prims.of_int (144))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (146))
                                                             (Prims.of_int (22)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.AssertWithBinders.fst"
                                                             (Prims.of_int (147))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (152))
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
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (57)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (152))
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
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (option_must
                                                                    rt
                                                                    "Unexpected: reduction produced an ill-formed term"))
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
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (option_must
                                                                    (Pulse_Readback.readback_ty
                                                                    rt1)
                                                                    "Unexpected: unable to readback unfolded term"))
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
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (150))
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
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
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
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (134)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
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
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (156)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (156)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (151))
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
                                                  (Prims.of_int (155))
                                                  (Prims.of_int (41))
                                                  (Prims.of_int (155))
                                                  (Prims.of_int (97)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                  (Prims.of_int (155))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (155))
                                                  (Prims.of_int (97)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.AssertWithBinders.fst"
                                                        (Prims.of_int (155))
                                                        (Prims.of_int (76))
                                                        (Prims.of_int (155))
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
                                                  (FStar_Tactics_V2_Builtins.term_to_string
                                                     t1))
                                               (fun uu___3 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___4 ->
                                                       Prims.strcat
                                                         "Cannot unfold "
                                                         (Prims.strcat uu___3
                                                            "")))))
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
                                (Prims.of_int (175)) (Prims.of_int (6))
                                (Prims.of_int (177)) (Prims.of_int (45)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (173)) (Prims.of_int (3))
                                (Prims.of_int (177)) (Prims.of_int (45)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.AssertWithBinders.fst"
                                      (Prims.of_int (177))
                                      (Prims.of_int (24))
                                      (Prims.of_int (177))
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
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Typing.post_hint_opt ->
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
                         (Prims.of_int (190)) (Prims.of_int (69))
                         (Prims.of_int (190)) (Prims.of_int (76)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.AssertWithBinders.fst"
                         (Prims.of_int (188)) (Prims.of_int (46))
                         (Prims.of_int (224)) (Prims.of_int (41)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> st.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                          { Pulse_Syntax_Base.hint_type = hint_type;
                            Pulse_Syntax_Base.binders = bs;
                            Pulse_Syntax_Base.v = v;
                            Pulse_Syntax_Base.t3 = body;_}
                          ->
                          (match hint_type with
                           | Pulse_Syntax_Base.ASSERT ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.AssertWithBinders.fst"
                                             (Prims.of_int (194))
                                             (Prims.of_int (13))
                                             (Prims.of_int (194))
                                             (Prims.of_int (38)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.AssertWithBinders.fst"
                                             (Prims.of_int (194))
                                             (Prims.of_int (41))
                                             (Prims.of_int (200))
                                             (Prims.of_int (52)))))
                                    (Obj.magic (infer_binder_types g bs v))
                                    (fun uu___1 ->
                                       (fun bs1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.AssertWithBinders.fst"
                                                        (Prims.of_int (195))
                                                        (Prims.of_int (29))
                                                        (Prims.of_int (195))
                                                        (Prims.of_int (76)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.AssertWithBinders.fst"
                                                        (Prims.of_int (194))
                                                        (Prims.of_int (41))
                                                        (Prims.of_int (200))
                                                        (Prims.of_int (52)))))
                                               (Obj.magic
                                                  (open_binders g bs1
                                                     (Pulse_Typing_Env.mk_env
                                                        (Pulse_Typing_Env.fstar_env
                                                           g)) v body))
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     match uu___1 with
                                                     | FStar_Pervasives.Mkdtuple3
                                                         (uvs, v1, body1) ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (54)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (52)))))
                                                              (Obj.magic
                                                                 (Pulse_Checker_Pure.check_vprop
                                                                    (
                                                                    Pulse_Typing_Env.push_env
                                                                    g uvs) v1))
                                                              (fun uu___2 ->
                                                                 (fun uu___2
                                                                    ->
                                                                    match uu___2
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
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover.prove
                                                                    g pre ()
                                                                    uvs v2 ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g1, nts,
                                                                    pre',
                                                                    k_frame)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (106)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (check1
                                                                    g1
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    (Pulse_Prover_Substs.nt_subst_term
                                                                    v2 nts)
                                                                    pre') ()
                                                                    post_hint
                                                                    (Pulse_Prover_Substs.nt_subst_st_term
                                                                    body1 nts)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
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
                                                                    (Pulse_Checker_Common.k_elab_trans
                                                                    g g1 g2
                                                                    pre
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Substs.nt_subst_term
                                                                    v2 nts)
                                                                    pre')
                                                                    pre''
                                                                    k_frame k))))))
                                                                    uu___3)))
                                                                   uu___2)))
                                                    uu___1))) uu___1))
                           | uu___1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.AssertWithBinders.fst"
                                             (Prims.of_int (203))
                                             (Prims.of_int (4))
                                             (Prims.of_int (203))
                                             (Prims.of_int (24)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.AssertWithBinders.fst"
                                             (Prims.of_int (204))
                                             (Prims.of_int (4))
                                             (Prims.of_int (224))
                                             (Prims.of_int (41)))))
                                    (Obj.magic (check_unfoldable g v))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          match bs with
                                          | uu___3::uu___4 ->
                                              Obj.magic
                                                (Pulse_Typing_Env.fail g
                                                   (FStar_Pervasives_Native.Some
                                                      (st.Pulse_Syntax_Base.range2))
                                                   "binders in fold and unfold are not yet supported")
                                          | [] ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.AssertWithBinders.fst"
                                                            (Prims.of_int (209))
                                                            (Prims.of_int (17))
                                                            (Prims.of_int (209))
                                                            (Prims.of_int (50)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.AssertWithBinders.fst"
                                                            (Prims.of_int (208))
                                                            (Prims.of_int (11))
                                                            (Prims.of_int (224))
                                                            (Prims.of_int (41)))))
                                                   (Obj.magic
                                                      (Pulse_Checker_Pure.instantiate_term_implicits
                                                         g v))
                                                   (fun uu___3 ->
                                                      (fun uu___3 ->
                                                         match uu___3 with
                                                         | (v1, uu___4) ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (11)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (41)))))
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
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (unfold_defs
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    v1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (v1,
                                                                    uu___6))))
                                                                   | 
                                                                   Pulse_Syntax_Base.FOLD
                                                                    ns ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (unfold_defs
                                                                    g ns v1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (uu___5,
                                                                    v1)))))
                                                                  (fun uu___5
                                                                    ->
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
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (41)))))
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
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (41)))))
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
                                                                    = body
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2)
                                                                    }))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun st1
                                                                    ->
                                                                    Obj.magic
                                                                    (check1 g
                                                                    pre ()
                                                                    post_hint
                                                                    st1))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                        uu___3))) uu___2))))
                     uu___)