open Prims
let (head_wild : Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders
        { Pulse_Syntax_Base.hint_type = Pulse_Syntax_Base.WILD;
          Pulse_Syntax_Base.binders = uu___; Pulse_Syntax_Base.t = uu___1;_}
        -> true
    | uu___ -> false
let (head_show_proof_state : Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun st ->
    match st.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders
        {
          Pulse_Syntax_Base.hint_type = Pulse_Syntax_Base.SHOW_PROOF_STATE
            uu___;
          Pulse_Syntax_Base.binders = uu___1; Pulse_Syntax_Base.t = uu___2;_}
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
                                (Prims.of_int (51)) (Prims.of_int (25))
                                (Prims.of_int (51)) (Prims.of_int (43)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (50)) (Prims.of_int (20))
                                (Prims.of_int (53)) (Prims.of_int (75)))))
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
                                   (refl_abs_binders body
                                      ((Pulse_Syntax_Base.mk_binder_ppname
                                          sort
                                          (Pulse_Syntax_Base.mk_ppname ppname
                                             (Pulse_RuntimeUtils.range_of_term
                                                t))) :: acc))) uu___)))
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
                                    (Prims.of_int (61)) (Prims.of_int (16))
                                    (Prims.of_int (61)) (Prims.of_int (50)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.AssertWithBinders.fst"
                                    (Prims.of_int (61)) (Prims.of_int (53))
                                    (Prims.of_int (81)) (Prims.of_int (40)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Pulse_RuntimeUtils.range_of_term v))
                           (fun uu___1 ->
                              (fun v_rng ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (62))
                                               (Prims.of_int (12))
                                               (Prims.of_int (62))
                                               (Prims.of_int (53)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (62))
                                               (Prims.of_int (56))
                                               (Prims.of_int (81))
                                               (Prims.of_int (40)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            Pulse_Typing_Env.push_context g
                                              "infer_binder_types" v_rng))
                                      (fun uu___1 ->
                                         (fun g1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (64))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (70))
                                                          (Prims.of_int (20)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (71))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (81))
                                                          (Prims.of_int (40)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       fun b ->
                                                         FStar_Reflection_V2_Builtins.pack_binder
                                                           {
                                                             FStar_Reflection_V2_Data.sort2
                                                               =
                                                               (b.Pulse_Syntax_Base.binder_ty);
                                                             FStar_Reflection_V2_Data.qual
                                                               =
                                                               FStar_Reflection_V2_Data.Q_Explicit;
                                                             FStar_Reflection_V2_Data.attrs
                                                               = [];
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
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (9)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (40)))))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___1 ->
                                                                  FStar_List_Tot_Base.fold_right
                                                                    (
                                                                    fun b ->
                                                                    fun tv ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Abs
                                                                    ((as_binder
                                                                    b), tv)))
                                                                    bs v))
                                                            (fun uu___1 ->
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
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.instantiate_term_implicits
                                                                    g1
                                                                    (Pulse_Syntax_Pure.wr
                                                                    abstraction
                                                                    v_rng)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    (inst_abstraction,
                                                                    uu___2)
                                                                    ->
                                                                    Obj.magic
                                                                    (refl_abs_binders
                                                                    inst_abstraction
                                                                    []))
                                                                    uu___1)))
                                                                 uu___1)))
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
                                            (Prims.of_int (90))
                                            (Prims.of_int (12))
                                            (Prims.of_int (90))
                                            (Prims.of_int (58)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.AssertWithBinders.fst"
                                            (Prims.of_int (90))
                                            (Prims.of_int (61))
                                            (Prims.of_int (98))
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
                                                       (Prims.of_int (91))
                                                       (Prims.of_int (12))
                                                       (Prims.of_int (91))
                                                       (Prims.of_int (34)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.AssertWithBinders.fst"
                                                       (Prims.of_int (91))
                                                       (Prims.of_int (37))
                                                       (Prims.of_int (98))
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
                                                                  (Prims.of_int (92))
                                                                  (Prims.of_int (13))
                                                                  (Prims.of_int (92))
                                                                  (Prims.of_int (72)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.AssertWithBinders.fst"
                                                                  (Prims.of_int (92))
                                                                  (Prims.of_int (75))
                                                                  (Prims.of_int (98))
                                                                  (Prims.of_int (77)))))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___1 ->
                                                               [FStar_Reflection_Typing.DT
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
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (45)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (98))
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
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (98))
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
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (98))
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
                  ((n + Prims.int_one), ((FStar_Reflection_Typing.ND (x, n))
                    :: ss))) bs (Prims.int_zero, []))
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
                          [FStar_Reflection_Typing.ND (x, n)]))) bs1 in
        let b = Pulse_Syntax_Base.mk_binder_ppname t name in b ::
          (close_binders bss)
let (unfold_all :
  Pulse_Typing_Env.env ->
    Prims.string Prims.list ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun names ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (120)) (Prims.of_int (13))
                   (Prims.of_int (120)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (120)) (Prims.of_int (26))
                   (Prims.of_int (122)) (Prims.of_int (5)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Typing.elab_env g))
          (fun uu___ ->
             (fun rg ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.AssertWithBinders.fst"
                              (Prims.of_int (121)) (Prims.of_int (12))
                              (Prims.of_int (121)) (Prims.of_int (66)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.AssertWithBinders.fst"
                              (Prims.of_int (121)) (Prims.of_int (8))
                              (Prims.of_int (121)) (Prims.of_int (9)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Builtins.norm_term_env rg
                           [FStar_Pervasives.primops;
                           FStar_Pervasives.iota;
                           FStar_Pervasives.delta_only names] t))
                     (fun t1 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t1))))
               uu___)
let (def_of_fv :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.fv ->
      (FStar_Reflection_Types.term FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun fv ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   match FStar_Reflection_V2_Builtins.lookup_typ g
                           (FStar_Reflection_V2_Builtins.inspect_fv fv)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some se ->
                       (match FStar_Reflection_V2_Builtins.inspect_sigelt se
                        with
                        | FStar_Reflection_V2_Data.Unk ->
                            FStar_Pervasives_Native.None
                        | FStar_Reflection_V2_Data.Sg_Let (uu___1, lbs) ->
                            FStar_List_Tot_Base.tryPick
                              (fun lb ->
                                 if
                                   (FStar_Reflection_V2_Builtins.inspect_fv
                                      (FStar_Reflection_V2_Builtins.inspect_lb
                                         lb).FStar_Reflection_V2_Data.lb_fv)
                                     =
                                     (FStar_Reflection_V2_Builtins.inspect_fv
                                        fv)
                                 then
                                   FStar_Pervasives_Native.Some
                                     ((FStar_Reflection_V2_Builtins.inspect_lb
                                         lb).FStar_Reflection_V2_Data.lb_def)
                                 else FStar_Pervasives_Native.None) lbs
                        | FStar_Reflection_V2_Data.Sg_Val (uu___1, uu___2, t)
                            -> FStar_Pervasives_Native.Some t
                        | FStar_Reflection_V2_Data.Sg_Inductive
                            (_nm, _univs, params, typ, uu___1) ->
                            FStar_Pervasives_Native.None)))) uu___1 uu___
let (unfold_head :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                 (Prims.of_int (147)) (Prims.of_int (13))
                 (Prims.of_int (147)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                 (Prims.of_int (148)) (Prims.of_int (4)) (Prims.of_int (168))
                 (Prims.of_int (89)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Typing.elab_env g))
        (fun uu___ ->
           (fun rg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.AssertWithBinders.fst"
                            (Prims.of_int (148)) (Prims.of_int (10))
                            (Prims.of_int (148)) (Prims.of_int (17)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.AssertWithBinders.fst"
                            (Prims.of_int (148)) (Prims.of_int (4))
                            (Prims.of_int (168)) (Prims.of_int (89)))))
                   (Obj.magic (FStar_Tactics_V2_SyntaxHelpers.hua t))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | FStar_Pervasives_Native.Some (fv, u, args) ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.AssertWithBinders.fst"
                                           (Prims.of_int (152))
                                           (Prims.of_int (14))
                                           (Prims.of_int (152))
                                           (Prims.of_int (91)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.AssertWithBinders.fst"
                                           (Prims.of_int (152))
                                           (Prims.of_int (10))
                                           (Prims.of_int (152))
                                           (Prims.of_int (11)))))
                                  (Obj.magic
                                     (FStar_Tactics_V2_Builtins.norm_term_env
                                        rg
                                        [FStar_Pervasives.hnf;
                                        FStar_Pervasives.zeta;
                                        FStar_Pervasives.delta_only
                                          [FStar_Reflection_V2_Builtins.implode_qn
                                             (FStar_Reflection_V2_Builtins.inspect_fv
                                                fv)]] t))
                                  (fun t1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 -> t1)))
                         | FStar_Pervasives_Native.None ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.AssertWithBinders.fst"
                                           (Prims.of_int (168))
                                           (Prims.of_int (8))
                                           (Prims.of_int (168))
                                           (Prims.of_int (89)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.AssertWithBinders.fst"
                                           (Prims.of_int (167))
                                           (Prims.of_int (6))
                                           (Prims.of_int (168))
                                           (Prims.of_int (89)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                 (Prims.of_int (168))
                                                 (Prims.of_int (68))
                                                 (Prims.of_int (168))
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
                                              t))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                Prims.strcat "Cannot unfold "
                                                  (Prims.strcat uu___1
                                                     ", the head is not an fvar")))))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
                                        Obj.magic
                                          (Pulse_Typing_Env.fail g
                                             (FStar_Pervasives_Native.Some
                                                (Pulse_RuntimeUtils.range_of_term
                                                   t)) uu___1)) uu___1)))
                        uu___))) uu___)
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
                   (Prims.of_int (172)) (Prims.of_int (12))
                   (Prims.of_int (172)) (Prims.of_int (27)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (172)) (Prims.of_int (30))
                   (Prims.of_int (179)) (Prims.of_int (5)))))
          (Obj.magic (unfold_head g t))
          (fun uu___ ->
             (fun t1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.AssertWithBinders.fst"
                              (Prims.of_int (174)) (Prims.of_int (6))
                              (Prims.of_int (176)) (Prims.of_int (40)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.AssertWithBinders.fst"
                              (Prims.of_int (177)) (Prims.of_int (6))
                              (Prims.of_int (179)) (Prims.of_int (5)))))
                     (match defs with
                      | FStar_Pervasives_Native.None ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___ -> t1)))
                      | FStar_Pervasives_Native.Some defs1 ->
                          Obj.magic (Obj.repr (unfold_all g defs1 t1)))
                     (fun uu___ ->
                        (fun t2 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.AssertWithBinders.fst"
                                         (Prims.of_int (178))
                                         (Prims.of_int (12))
                                         (Prims.of_int (178))
                                         (Prims.of_int (63)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.AssertWithBinders.fst"
                                         (Prims.of_int (178))
                                         (Prims.of_int (8))
                                         (Prims.of_int (178))
                                         (Prims.of_int (9)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Builtins.norm_term_env
                                      (Pulse_Typing.elab_env g)
                                      [FStar_Pervasives.hnf;
                                      FStar_Pervasives.iota;
                                      FStar_Pervasives.primops] t2))
                                (fun t3 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ -> t3)))) uu___))) uu___)
let (check_unfoldable :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun v ->
           match Pulse_Syntax_Pure.inspect_term v with
           | Pulse_Syntax_Pure.Tm_FStar uu___ ->
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
                                (Prims.of_int (187)) (Prims.of_int (6))
                                (Prims.of_int (189)) (Prims.of_int (45)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (185)) (Prims.of_int (3))
                                (Prims.of_int (189)) (Prims.of_int (45)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.AssertWithBinders.fst"
                                      (Prims.of_int (189))
                                      (Prims.of_int (24))
                                      (Prims.of_int (189))
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
                                     (Pulse_RuntimeUtils.range_of_term v))
                                  uu___1)) uu___1)))) uu___1 uu___
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
                 (Prims.of_int (193)) (Prims.of_int (17))
                 (Prims.of_int (193)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                 (Prims.of_int (192)) (Prims.of_int (40))
                 (Prims.of_int (203)) (Prims.of_int (47)))))
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
                                (Prims.of_int (195)) (Prims.of_int (4))
                                (Prims.of_int (195)) (Prims.of_int (36)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.AssertWithBinders.fst"
                                (Prims.of_int (197)) (Prims.of_int (2))
                                (Prims.of_int (203)) (Prims.of_int (47)))))
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
                                              [FStar_Reflection_Typing.NT
                                                 (((FStar_Reflection_V2_Builtins.inspect_namedv
                                                      n).FStar_Reflection_V2_Data.uniq),
                                                   (Pulse_Syntax_Pure.wr rhs
                                                      (Pulse_RuntimeUtils.range_of_term
                                                         t)))])))
                             | uu___1 ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Visit.visit_tm visitor t)))
                            uu___1))) uu___)
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
                 (Prims.of_int (209)) (Prims.of_int (12))
                 (Prims.of_int (209)) (Prims.of_int (30)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                 (Prims.of_int (209)) (Prims.of_int (33))
                 (Prims.of_int (220)) (Prims.of_int (38)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Syntax_Pure.vprop_as_list goal))
        (fun uu___ ->
           (fun tms ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.AssertWithBinders.fst"
                            (Prims.of_int (210)) (Prims.of_int (13))
                            (Prims.of_int (210)) (Prims.of_int (79)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.AssertWithBinders.fst"
                            (Prims.of_int (211)) (Prims.of_int (41))
                            (Prims.of_int (220)) (Prims.of_int (38)))))
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
                                       (Prims.of_int (213))
                                       (Prims.of_int (4))
                                       (Prims.of_int (218))
                                       (Prims.of_int (14)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.AssertWithBinders.fst"
                                       (Prims.of_int (211))
                                       (Prims.of_int (41))
                                       (Prims.of_int (220))
                                       (Prims.of_int (38)))))
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
                                          ((Pulse_Syntax_Pure.list_as_vprop
                                              lhs),
                                            (Pulse_Syntax_Pure.list_as_vprop
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
              (match FStar_Reflection_V2_Builtins.inspect_ln e1 with
               | FStar_Reflection_V2_Data.Tv_Var n ->
                   let nv = FStar_Reflection_V2_Builtins.inspect_namedv n in
                   as_subst p1
                     ((FStar_Reflection_Typing.NT
                         ((nv.FStar_Reflection_V2_Data.uniq), e2)) :: out)
                     ((nv.FStar_Reflection_V2_Data.uniq) :: domain)
                     (FStar_Set.union codomain
                        (Pulse_Syntax_Naming.freevars e2))
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
                                    (Prims.of_int (256)) (Prims.of_int (6))
                                    (Prims.of_int (260)) (Prims.of_int (9)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.AssertWithBinders.fst"
                                    (Prims.of_int (261)) (Prims.of_int (6))
                                    (Prims.of_int (264)) (Prims.of_int (12)))))
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
                                                   (Prims.of_int (258))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (258))
                                                   (Prims.of_int (68)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.AssertWithBinders.fst"
                                                   (Prims.of_int (258))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (259))
                                                   (Prims.of_int (68)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.AssertWithBinders.fst"
                                                         (Prims.of_int (258))
                                                         (Prims.of_int (15))
                                                         (Prims.of_int (258))
                                                         (Prims.of_int (67)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.AssertWithBinders.fst"
                                                         (Prims.of_int (258))
                                                         (Prims.of_int (10))
                                                         (Prims.of_int (258))
                                                         (Prims.of_int (68)))))
                                                (Obj.magic
                                                   (Pulse_Checker_Pure.instantiate_term_implicits
                                                      g e1))
                                                (fun uu___2 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        FStar_Pervasives_Native.fst
                                                          uu___2))))
                                          (fun uu___2 ->
                                             (fun uu___2 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.AssertWithBinders.fst"
                                                              (Prims.of_int (259))
                                                              (Prims.of_int (10))
                                                              (Prims.of_int (259))
                                                              (Prims.of_int (68)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.AssertWithBinders.fst"
                                                              (Prims.of_int (258))
                                                              (Prims.of_int (10))
                                                              (Prims.of_int (259))
                                                              (Prims.of_int (68)))))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (67)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (68)))))
                                                           (Obj.magic
                                                              (Pulse_Checker_Pure.instantiate_term_implicits
                                                                 g e2))
                                                           (fun uu___3 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   FStar_Pervasives_Native.fst
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
                                               (Prims.of_int (262))
                                               (Prims.of_int (19))
                                               (Prims.of_int (262))
                                               (Prims.of_int (54)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.AssertWithBinders.fst"
                                               (Prims.of_int (261))
                                               (Prims.of_int (6))
                                               (Prims.of_int (264))
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
                                                              (Prims.of_int (263))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (263))
                                                              (Prims.of_int (106)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.AssertWithBinders.fst"
                                                              (Prims.of_int (264))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (264))
                                                              (Prims.of_int (12)))))
                                                     (Obj.magic
                                                        (debug_log g
                                                           (fun uu___2 ->
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (105)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (263))
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
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (263))
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
                   (Prims.of_int (275)) (Prims.of_int (35))
                   (Prims.of_int (275)) (Prims.of_int (42)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (275)) Prims.int_one (Prims.of_int (301))
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
                                  (Prims.of_int (276)) (Prims.of_int (65))
                                  (Prims.of_int (276)) (Prims.of_int (67)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.AssertWithBinders.fst"
                                  (Prims.of_int (275)) (Prims.of_int (45))
                                  (Prims.of_int (301)) (Prims.of_int (3)))))
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
                                   Pulse_Syntax_Base.t = body;_} ->
                                   (match (bs, goal) with
                                    | (uu___2::uu___3,
                                       FStar_Pervasives_Native.None) ->
                                        Obj.magic
                                          (Obj.repr
                                             (Pulse_Typing_Env.fail g
                                                (FStar_Pervasives_Native.Some
                                                   (st.Pulse_Syntax_Base.range1))
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
                                                            Pulse_Syntax_Base.t
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
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    (ht.Pulse_Syntax_Base.t)
                                                                    });
                                                                Pulse_Syntax_Base.range1
                                                                  =
                                                                  (st.Pulse_Syntax_Base.range1);
                                                                Pulse_Syntax_Base.effect_tag
                                                                  =
                                                                  (st.Pulse_Syntax_Base.effect_tag)
                                                              }
                                                          });
                                                     Pulse_Syntax_Base.range1
                                                       =
                                                       (st.Pulse_Syntax_Base.range1);
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
                                                         (Prims.of_int (292))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (292))
                                                         (Prims.of_int (42)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.AssertWithBinders.fst"
                                                         (Prims.of_int (290))
                                                         (Prims.of_int (15))
                                                         (Prims.of_int (294))
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
                                                                    = rhs;
                                                                    Pulse_Syntax_Base.tac_opt1
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st.Pulse_Syntax_Base.effect_tag)
                                                                    };
                                                                    Pulse_Syntax_Base.body1
                                                                    = body
                                                                   });
                                                              Pulse_Syntax_Base.range1
                                                                =
                                                                (st.Pulse_Syntax_Base.range1);
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
                                                         (Prims.of_int (297))
                                                         (Prims.of_int (20))
                                                         (Prims.of_int (297))
                                                         (Prims.of_int (56)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.AssertWithBinders.fst"
                                                         (Prims.of_int (296))
                                                         (Prims.of_int (21))
                                                         (Prims.of_int (301))
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
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (45)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (300))
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
                                                                    = rhs;
                                                                    Pulse_Syntax_Base.tac_opt1
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st.Pulse_Syntax_Base.effect_tag)
                                                                    };
                                                                    Pulse_Syntax_Base.body1
                                                                    = body
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1);
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
                   (Prims.of_int (308)) (Prims.of_int (35))
                   (Prims.of_int (308)) (Prims.of_int (42)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.AssertWithBinders.fst"
                   (Prims.of_int (308)) Prims.int_one (Prims.of_int (340))
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
                                  (Prims.of_int (309)) (Prims.of_int (31))
                                  (Prims.of_int (309)) (Prims.of_int (33)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.AssertWithBinders.fst"
                                  (Prims.of_int (308)) (Prims.of_int (45))
                                  (Prims.of_int (340)) (Prims.of_int (23)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> ht))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               match uu___1 with
                               | { Pulse_Syntax_Base.hint_type = uu___2;
                                   Pulse_Syntax_Base.binders = bs;
                                   Pulse_Syntax_Base.t = body;_} ->
                                   (match bs with
                                    | [] ->
                                        Obj.magic
                                          (Pulse_Typing_Env.fail g
                                             (FStar_Pervasives_Native.Some
                                                (st.Pulse_Syntax_Base.range1))
                                             "A wildcard must have at least one binder")
                                    | uu___3 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.AssertWithBinders.fst"
                                                      (Prims.of_int (315))
                                                      (Prims.of_int (17))
                                                      (Prims.of_int (315))
                                                      (Prims.of_int (34)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.AssertWithBinders.fst"
                                                      (Prims.of_int (315))
                                                      (Prims.of_int (37))
                                                      (Prims.of_int (340))
                                                      (Prims.of_int (23)))))
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___4 ->
                                                   Pulse_Syntax_Pure.vprop_as_list
                                                     pre))
                                             (fun uu___4 ->
                                                (fun vprops ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (316))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (318))
                                                                 (Prims.of_int (62)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.AssertWithBinders.fst"
                                                                 (Prims.of_int (315))
                                                                 (Prims.of_int (37))
                                                                 (Prims.of_int (340))
                                                                 (Prims.of_int (23)))))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              FStar_List_Tot_Base.partition
                                                                (fun v ->
                                                                   Pulse_Syntax_Pure.uu___is_Tm_ExistsSL
                                                                    (Pulse_Syntax_Pure.inspect_term
                                                                    v))
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
                                                                    (st.Pulse_Syntax_Base.range1))
                                                                    "Binding names with a wildcard requires exactly one existential quantifier in the goal.")
                                                                   | 
                                                                   uu___5::uu___6::uu___7
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.range1))
                                                                    "Binding names with a wildcard requires exactly one existential quantifier in the goal.")
                                                                   | 
                                                                   ex1::[] ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (340))
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
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    (ht.Pulse_Syntax_Base.t)
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st.Pulse_Syntax_Base.effect_tag)
                                                                    })))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    Pulse_Syntax_Pure.inspect_term
                                                                    t
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Pure.Tm_ExistsSL
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
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (337))
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
                                                                    Pulse_Show.tac_showable_r_term
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
                                                                    (st.Pulse_Syntax_Base.range1))
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
                                        (Prims.of_int (351))
                                        (Prims.of_int (12))
                                        (Prims.of_int (351))
                                        (Prims.of_int (34)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.AssertWithBinders.fst"
                                        (Prims.of_int (351))
                                        (Prims.of_int (37))
                                        (Prims.of_int (356))
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
                                                   (Prims.of_int (352))
                                                   (Prims.of_int (17))
                                                   (Prims.of_int (352))
                                                   (Prims.of_int (48)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.AssertWithBinders.fst"
                                                   (Prims.of_int (352))
                                                   (Prims.of_int (51))
                                                   (Prims.of_int (356))
                                                   (Prims.of_int (37)))))
                                          (Obj.magic
                                             (Pulse_Syntax_Base.ppname_for_uvar
                                                b.Pulse_Syntax_Base.binder_ppname))
                                          (fun uu___ ->
                                             (fun ppname ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.AssertWithBinders.fst"
                                                              (Prims.of_int (353))
                                                              (Prims.of_int (13))
                                                              (Prims.of_int (353))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.AssertWithBinders.fst"
                                                              (Prims.of_int (353))
                                                              (Prims.of_int (42))
                                                              (Prims.of_int (356))
                                                              (Prims.of_int (37)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___ ->
                                                           Pulse_Syntax_Naming.open_comp_nv
                                                             c (ppname, x)))
                                                     (fun uu___ ->
                                                        (fun ct ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (55)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (37)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun uu___
                                                                    ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    uvs x
                                                                    ppname
                                                                    b.Pulse_Syntax_Base.binder_ty))
                                                                (fun uu___ ->
                                                                   (fun uvs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax_Pure.tm_pureapp
                                                                    v qopt
                                                                    (Pulse_Syntax_Pure.tm_var
                                                                    {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    = ppname
                                                                    })))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun v1
                                                                    ->
                                                                    Obj.magic
                                                                    (add_rem_uvs
                                                                    g
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    ct) uvs1
                                                                    v1))
                                                                    uu___)))
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
                           (Prims.of_int (369)) (Prims.of_int (10))
                           (Prims.of_int (369)) (Prims.of_int (48)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.AssertWithBinders.fst"
                           (Prims.of_int (369)) (Prims.of_int (51))
                           (Prims.of_int (488)) (Prims.of_int (50)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Typing_Env.push_context g "check_assert"
                          st.Pulse_Syntax_Base.range1))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.AssertWithBinders.fst"
                                      (Prims.of_int (371))
                                      (Prims.of_int (66))
                                      (Prims.of_int (371))
                                      (Prims.of_int (73)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.AssertWithBinders.fst"
                                      (Prims.of_int (369))
                                      (Prims.of_int (51))
                                      (Prims.of_int (488))
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
                                         Pulse_Syntax_Base.t = body;_}
                                       ->
                                       (match hint_type with
                                        | Pulse_Syntax_Base.WILD ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (375))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (375))
                                                          (Prims.of_int (32)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (376))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (376))
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
                                                          (Prims.of_int (381))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (384))
                                                          (Prims.of_int (5)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (385))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (385))
                                                          (Prims.of_int (36)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (382))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (383))
                                                                (Prims.of_int (48)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (381))
                                                                (Prims.of_int (14))
                                                                (Prims.of_int (384))
                                                                (Prims.of_int (5)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (48)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (48)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (48)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (48)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Pure.canon_vprop_print
                                                                    pre))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    uu___1))
                                                                    uu___1)))
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
                                                          (Prims.of_int (387))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (387))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (388))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (388))
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
                                              Pulse_Syntax_Base.t2 = t2;
                                              Pulse_Syntax_Base.tac_opt =
                                                tac_opt;_}
                                            ->
                                            (match bs with
                                             | [] ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (393))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (393))
                                                               (Prims.of_int (61)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (394))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (395))
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
                                                                    = t2;
                                                                    Pulse_Syntax_Base.tac_opt1
                                                                    = tac_opt
                                                                   });
                                                              Pulse_Syntax_Base.range1
                                                                =
                                                                (st.Pulse_Syntax_Base.range1);
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
                                                                   Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1);
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
                                                               (Prims.of_int (397))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (397))
                                                               (Prims.of_int (61)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.AssertWithBinders.fst"
                                                               (Prims.of_int (397))
                                                               (Prims.of_int (66))
                                                               (Prims.of_int (400))
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
                                                                    = t2;
                                                                    Pulse_Syntax_Base.tac_opt1
                                                                    = tac_opt
                                                                   });
                                                              Pulse_Syntax_Base.range1
                                                                =
                                                                (st.Pulse_Syntax_Base.range1);
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
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (88)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (400))
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
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1);
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
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (113)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (400))
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
                                                                    Pulse_Syntax_Base.t
                                                                    = body1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1);
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
                                                          (Prims.of_int (404))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (404))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (404))
                                                          (Prims.of_int (37))
                                                          (Prims.of_int (420))
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
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (38)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (420))
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
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (90)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (420))
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
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (420))
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
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (420))
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
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (420))
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
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (check1
                                                                    g11
                                                                    (Pulse_Syntax_Pure.tm_star
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
                                                          (Prims.of_int (426))
                                                          (Prims.of_int (42))
                                                          (Prims.of_int (428))
                                                          (Prims.of_int (53)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (424))
                                                          (Prims.of_int (26))
                                                          (Prims.of_int (488))
                                                          (Prims.of_int (50)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (427))
                                                                (Prims.of_int (15))
                                                                (Prims.of_int (427))
                                                                (Prims.of_int (40)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (428))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (428))
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
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (24)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (437))
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
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (443))
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
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (446))
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
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (448))
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
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_BreakVC.break_vc
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g1)
                                                                    "fold"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    lhs1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "lhs:")
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    rhs1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "rhs:")
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    [uu___8]))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___7 ::
                                                                    uu___8))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    (Pulse_PP.text
                                                                    "Elaborated fold/unfold to rewrite")
                                                                    :: uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun msg
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.info_doc_env
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.range1))
                                                                    msg))
                                                                    uu___7)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (473))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (473))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t11
                                                                    = lhs1;
                                                                    Pulse_Syntax_Base.t21
                                                                    = rhs1;
                                                                    Pulse_Syntax_Base.tac_opt1
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Reflection_Util.vprop_equiv_norm_tm)
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    Pulse_Syntax_Base.STT_Ghost)
                                                                    }))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun rw
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    (Pulse_Syntax_Base.as_binder
                                                                    (Pulse_Syntax_Pure.wr
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])))
                                                                    st.Pulse_Syntax_Base.range1));
                                                                    Pulse_Syntax_Base.head1
                                                                    = rw;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (body1.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun st1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match bs1
                                                                    with
                                                                    | 
                                                                    [] -> st1
                                                                    | 
                                                                    uu___9 ->
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
                                                                    Pulse_Syntax_Base.t
                                                                    = st1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st1.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st1.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun st2
                                                                    ->
                                                                    Obj.magic
                                                                    (check1
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    st2))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
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
                                                          (Prims.of_int (426))
                                                          (Prims.of_int (42))
                                                          (Prims.of_int (428))
                                                          (Prims.of_int (53)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.AssertWithBinders.fst"
                                                          (Prims.of_int (424))
                                                          (Prims.of_int (26))
                                                          (Prims.of_int (488))
                                                          (Prims.of_int (50)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (427))
                                                                (Prims.of_int (15))
                                                                (Prims.of_int (427))
                                                                (Prims.of_int (40)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.AssertWithBinders.fst"
                                                                (Prims.of_int (428))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (428))
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
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (24)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (437))
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
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (443))
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
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (446))
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
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (448))
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
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (488))
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
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_BreakVC.break_vc
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g1)
                                                                    "fold"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    lhs1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "lhs:")
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    rhs1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "rhs:")
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    [uu___8]))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___7 ::
                                                                    uu___8))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    (Pulse_PP.text
                                                                    "Elaborated fold/unfold to rewrite")
                                                                    :: uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun msg
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.info_doc_env
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.range1))
                                                                    msg))
                                                                    uu___7)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (473))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (473))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t11
                                                                    = lhs1;
                                                                    Pulse_Syntax_Base.t21
                                                                    = rhs1;
                                                                    Pulse_Syntax_Base.tac_opt1
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Reflection_Util.vprop_equiv_norm_tm)
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (Pulse_Syntax_Base.as_effect_hint
                                                                    Pulse_Syntax_Base.STT_Ghost)
                                                                    }))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun rw
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    (Pulse_Syntax_Base.as_binder
                                                                    (Pulse_Syntax_Pure.wr
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])))
                                                                    st.Pulse_Syntax_Base.range1));
                                                                    Pulse_Syntax_Base.head1
                                                                    = rw;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (body1.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun st1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.AssertWithBinders.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match bs1
                                                                    with
                                                                    | 
                                                                    [] -> st1
                                                                    | 
                                                                    uu___9 ->
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
                                                                    Pulse_Syntax_Base.t
                                                                    = st1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (st1.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (st1.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun st2
                                                                    ->
                                                                    Obj.magic
                                                                    (check1
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    st2))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
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