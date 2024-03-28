open Prims
let rec (equational : Pulse_Syntax_Base.term -> Prims.bool) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_Match (uu___, uu___1, uu___2) -> true
    | FStar_Reflection_V2_Data.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
        equational t1
    | FStar_Reflection_V2_Data.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
        equational t1
    | uu___ -> false
let (type_of_fv :
  Pulse_Typing_Env.env ->
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
                   match FStar_Reflection_V2_Builtins.lookup_typ
                           (Pulse_Typing_Env.fstar_env g)
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
                                         lb).FStar_Reflection_V2_Data.lb_typ)
                                 else FStar_Pervasives_Native.None) lbs
                        | FStar_Reflection_V2_Data.Sg_Val (uu___1, uu___2, t)
                            -> FStar_Pervasives_Native.Some t
                        | FStar_Reflection_V2_Data.Sg_Inductive
                            (_nm, _univs, params, typ, uu___1) ->
                            FStar_Pervasives_Native.None)))) uu___1 uu___
let (is_smt_fallback : FStar_Reflection_Types.term -> Prims.bool) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_FVar fv ->
        let name = FStar_Reflection_V2_Builtins.inspect_fv fv in
        (name = ["Steel"; "Effect"; "Common"; "smt_fallback"]) ||
          (name = ["Pulse"; "Lib"; "Core"; "equate_by_smt"])
    | uu___ -> false
let (eligible_for_smt_equality :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      fun t1 ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                   (Prims.of_int (109)) (Prims.of_int (31))
                   (Prims.of_int (109)) (Prims.of_int (61)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                   (Prims.of_int (109)) (Prims.of_int (64))
                   (Prims.of_int (168)) (Prims.of_int (31)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> fun uu___1 -> (equational t0) || (equational t1)))
          (fun uu___ ->
             (fun either_equational ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.Match.fst"
                              (Prims.of_int (111)) (Prims.of_int (6))
                              (Prims.of_int (114)) (Prims.of_int (18)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.Match.fst"
                              (Prims.of_int (116)) (Prims.of_int (4))
                              (Prims.of_int (168)) (Prims.of_int (31)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           fun t01 ->
                             fun t11 ->
                               match ((FStar_Reflection_V2_Builtins.inspect_ln
                                         t01),
                                       (FStar_Reflection_V2_Builtins.inspect_ln
                                          t11))
                               with
                               | (FStar_Reflection_V2_Data.Tv_App
                                  (h0, uu___1),
                                  FStar_Reflection_V2_Data.Tv_App
                                  (h1, uu___2)) ->
                                   FStar_Reflection_V2_TermEq.term_eq h0 h1
                               | uu___1 -> false))
                     (fun uu___ ->
                        (fun head_eq ->
                           match ((Pulse_Syntax_Pure.inspect_term t0),
                                   (Pulse_Syntax_Pure.inspect_term t1))
                           with
                           | (FStar_Pervasives_Native.Some
                              (Pulse_Syntax_Pure.Tm_ForallSL
                              (uu___, uu___1, uu___2)),
                              FStar_Pervasives_Native.Some
                              (Pulse_Syntax_Pure.Tm_ForallSL
                              (uu___3, uu___4, uu___5))) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___6 -> true)))
                           | uu___ ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Prover.Match.fst"
                                                (Prims.of_int (119))
                                                (Prims.of_int (22))
                                                (Prims.of_int (119))
                                                (Prims.of_int (41)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Prover.Match.fst"
                                                (Prims.of_int (118))
                                                (Prims.of_int (11))
                                                (Prims.of_int (167))
                                                (Prims.of_int (5)))))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             FStar_Reflection_V2_Derived.collect_app_ln
                                               t0))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             match uu___1 with
                                             | (h0, args0) ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Prover.Match.fst"
                                                               (Prims.of_int (120))
                                                               (Prims.of_int (22))
                                                               (Prims.of_int (120))
                                                               (Prims.of_int (41)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Prover.Match.fst"
                                                               (Prims.of_int (119))
                                                               (Prims.of_int (44))
                                                               (Prims.of_int (166))
                                                               (Prims.of_int (31)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___2 ->
                                                            FStar_Reflection_V2_Derived.collect_app_ln
                                                              t1))
                                                      (fun uu___2 ->
                                                         (fun uu___2 ->
                                                            match uu___2 with
                                                            | (h1, args1) ->
                                                                if
                                                                  (FStar_Reflection_V2_TermEq.term_eq
                                                                    h0 h1) &&
                                                                    (
                                                                    (FStar_List_Tot_Base.length
                                                                    args0) =
                                                                    (FStar_List_Tot_Base.length
                                                                    args1))
                                                                then
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (match 
                                                                    FStar_Reflection_V2_Builtins.inspect_ln
                                                                    h0
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Data.Tv_FVar
                                                                    fv ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (type_of_fv
                                                                    g fv))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    either_equational
                                                                    ()
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    t ->
                                                                    (match 
                                                                    FStar_Reflection_V2_Derived.collect_arr_ln_bs
                                                                    t
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    uu___5)
                                                                    ->
                                                                    (match 
                                                                    FStar_List_Tot_Base.fold_right
                                                                    (fun b ->
                                                                    fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (some_fallbacks,
                                                                    bs1) ->
                                                                    if
                                                                    FStar_List_Tot_Base.existsb
                                                                    is_smt_fallback
                                                                    (FStar_Reflection_V2_Builtins.inspect_binder
                                                                    b).FStar_Reflection_V2_Data.attrs
                                                                    then
                                                                    (true,
                                                                    (true ::
                                                                    bs1))
                                                                    else
                                                                    (some_fallbacks,
                                                                    (false ::
                                                                    bs1))) bs
                                                                    (false,
                                                                    [])
                                                                    with
                                                                    | 
                                                                    (some_fallbacks,
                                                                    fallbacks)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    some_fallbacks
                                                                    then
                                                                    head_eq
                                                                    t0 t1
                                                                    else
                                                                    (let rec aux
                                                                    args01
                                                                    args11
                                                                    fallbacks1
                                                                    =
                                                                    match 
                                                                    (args01,
                                                                    args11,
                                                                    fallbacks1)
                                                                    with
                                                                    | 
                                                                    ((a0,
                                                                    uu___7)::args02,
                                                                    (a1,
                                                                    uu___8)::args12,
                                                                    b::fallbacks2)
                                                                    ->
                                                                    if b
                                                                    then
                                                                    aux
                                                                    args02
                                                                    args12
                                                                    fallbacks2
                                                                    else
                                                                    if
                                                                    Prims.op_Negation
                                                                    (FStar_Reflection_V2_TermEq.term_eq
                                                                    a0 a1)
                                                                    then
                                                                    false
                                                                    else
                                                                    aux
                                                                    args02
                                                                    args12
                                                                    fallbacks2
                                                                    | 
                                                                    ([], [],
                                                                    []) ->
                                                                    true
                                                                    | 
                                                                    uu___7 ->
                                                                    either_equational
                                                                    () in
                                                                    aux args0
                                                                    args1
                                                                    fallbacks))))))
                                                                    | 
                                                                    FStar_Reflection_V2_Data.Tv_UInst
                                                                    (fv,
                                                                    uu___3)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (type_of_fv
                                                                    g fv))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    either_equational
                                                                    ()
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    t ->
                                                                    (match 
                                                                    FStar_Reflection_V2_Derived.collect_arr_ln_bs
                                                                    t
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    uu___6)
                                                                    ->
                                                                    (match 
                                                                    FStar_List_Tot_Base.fold_right
                                                                    (fun b ->
                                                                    fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (some_fallbacks,
                                                                    bs1) ->
                                                                    if
                                                                    FStar_List_Tot_Base.existsb
                                                                    is_smt_fallback
                                                                    (FStar_Reflection_V2_Builtins.inspect_binder
                                                                    b).FStar_Reflection_V2_Data.attrs
                                                                    then
                                                                    (true,
                                                                    (true ::
                                                                    bs1))
                                                                    else
                                                                    (some_fallbacks,
                                                                    (false ::
                                                                    bs1))) bs
                                                                    (false,
                                                                    [])
                                                                    with
                                                                    | 
                                                                    (some_fallbacks,
                                                                    fallbacks)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    some_fallbacks
                                                                    then
                                                                    head_eq
                                                                    t0 t1
                                                                    else
                                                                    (let rec aux
                                                                    args01
                                                                    args11
                                                                    fallbacks1
                                                                    =
                                                                    match 
                                                                    (args01,
                                                                    args11,
                                                                    fallbacks1)
                                                                    with
                                                                    | 
                                                                    ((a0,
                                                                    uu___8)::args02,
                                                                    (a1,
                                                                    uu___9)::args12,
                                                                    b::fallbacks2)
                                                                    ->
                                                                    if b
                                                                    then
                                                                    aux
                                                                    args02
                                                                    args12
                                                                    fallbacks2
                                                                    else
                                                                    if
                                                                    Prims.op_Negation
                                                                    (FStar_Reflection_V2_TermEq.term_eq
                                                                    a0 a1)
                                                                    then
                                                                    false
                                                                    else
                                                                    aux
                                                                    args02
                                                                    args12
                                                                    fallbacks2
                                                                    | 
                                                                    ([], [],
                                                                    []) ->
                                                                    true
                                                                    | 
                                                                    uu___8 ->
                                                                    either_equational
                                                                    () in
                                                                    aux args0
                                                                    args1
                                                                    fallbacks))))))
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    either_equational
                                                                    ()))))
                                                                else
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    either_equational
                                                                    ()))))
                                                           uu___2))) uu___1)))
                           | uu___ ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 -> either_equational ()))))
                          uu___))) uu___)
let (refl_uvar :
  FStar_Reflection_Types.term ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.var FStar_Pervasives_Native.option)
  =
  fun t ->
    fun uvs ->
      match FStar_Reflection_V2_Builtins.inspect_ln t with
      | FStar_Reflection_V2_Data.Tv_Var v ->
          let uu___ = FStar_Reflection_V2_Builtins.inspect_namedv v in
          (match uu___ with
           | { FStar_Reflection_V2_Data.uniq = n;
               FStar_Reflection_V2_Data.sort = uu___1;
               FStar_Reflection_V2_Data.ppname = uu___2;_} ->
               if Pulse_Typing_Env.contains uvs n
               then FStar_Pervasives_Native.Some n
               else FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None
let (is_uvar :
  Pulse_Syntax_Base.term ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.var FStar_Pervasives_Native.option)
  = fun t -> fun uvs -> refl_uvar t uvs
let (contains_uvar :
  Pulse_Syntax_Base.term ->
    Pulse_Typing_Env.env ->
      Pulse_Typing_Env.env ->
        (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun t ->
           fun uvs ->
             fun g ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       Prims.op_Negation
                         (Pulse_Typing_Env.check_disjoint uvs
                            (Pulse_Syntax_Naming.freevars t))))) uu___2
          uu___1 uu___
let (is_reveal_uvar :
  Pulse_Syntax_Base.term ->
    Pulse_Typing_Env.env ->
      (Pulse_Syntax_Base.universe * Pulse_Syntax_Base.term *
        Pulse_Syntax_Base.var) FStar_Pervasives_Native.option)
  =
  fun t ->
    fun uvs ->
      match Pulse_Syntax_Pure.is_pure_app t with
      | FStar_Pervasives_Native.Some (hd, FStar_Pervasives_Native.None, arg)
          ->
          (match Pulse_Syntax_Pure.is_pure_app hd with
           | FStar_Pervasives_Native.Some
               (hd1, FStar_Pervasives_Native.Some
                (Pulse_Syntax_Base.Implicit), ty)
               ->
               let arg_uvar_index_opt = is_uvar arg uvs in
               (match arg_uvar_index_opt with
                | FStar_Pervasives_Native.Some n ->
                    (match Pulse_Syntax_Pure.is_fvar hd1 with
                     | FStar_Pervasives_Native.Some (l, u::[]) ->
                         if l = Pulse_Reflection_Util.reveal_lid
                         then FStar_Pervasives_Native.Some (u, ty, n)
                         else FStar_Pervasives_Native.None
                     | uu___ -> FStar_Pervasives_Native.None)
                | uu___ -> FStar_Pervasives_Native.None)
           | uu___ -> FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None
let (is_reveal : Pulse_Syntax_Base.term -> Prims.bool) =
  fun t ->
    match Pulse_Syntax_Pure.leftmost_head t with
    | FStar_Pervasives_Native.Some hd ->
        (match Pulse_Syntax_Pure.is_fvar hd with
         | FStar_Pervasives_Native.Some (l, uu___::[]) ->
             l = Pulse_Reflection_Util.reveal_lid
         | uu___ -> false)
    | uu___ -> false
let (try_solve_uvars :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          (Pulse_Checker_Prover_Substs.ss_t, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun p ->
        fun q ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                     (Prims.of_int (219)) (Prims.of_int (12))
                     (Prims.of_int (230)) (Prims.of_int (8)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                     (Prims.of_int (230)) (Prims.of_int (11))
                     (Prims.of_int (257)) (Prims.of_int (10)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Match.fst"
                           (Prims.of_int (219)) (Prims.of_int (12))
                           (Prims.of_int (221)) (Prims.of_int (12)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Match.fst"
                           (Prims.of_int (219)) (Prims.of_int (12))
                           (Prims.of_int (230)) (Prims.of_int (8)))))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.Match.fst"
                                 (Prims.of_int (219)) (Prims.of_int (12))
                                 (Prims.of_int (220)) (Prims.of_int (27)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.Match.fst"
                                 (Prims.of_int (219)) (Prims.of_int (12))
                                 (Prims.of_int (221)) (Prims.of_int (12)))))
                        (Obj.magic
                           (Pulse_Typing_Env.bindings_with_ppname uvs))
                        (fun uu___ ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 -> FStar_List_Tot_Base.rev uu___))))
                  (fun uu___ ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          FStar_List_Tot_Base.map
                            (fun uu___2 ->
                               match uu___2 with
                               | ({ Pulse_Syntax_Base.name = name;
                                    Pulse_Syntax_Base.range = uu___3;_},
                                  x, t) ->
                                   ((FStar_Reflection_V2_Builtins.pack_namedv
                                       (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv
                                          {
                                            FStar_Reflection_V2_Data.uniq1 =
                                              x;
                                            FStar_Reflection_V2_Data.sort3 =
                                              (Pulse_Elaborate_Pure.elab_term
                                                 t);
                                            FStar_Reflection_V2_Data.ppname3
                                              = name
                                          })),
                                     (Pulse_Elaborate_Pure.elab_term t)))
                            uu___))))
            (fun uu___ ->
               (fun uvs1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.fst"
                                (Prims.of_int (232)) (Prims.of_int (18))
                                (Prims.of_int (233)) (Prims.of_int (61)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.fst"
                                (Prims.of_int (230)) (Prims.of_int (11))
                                (Prims.of_int (257)) (Prims.of_int (10)))))
                       (Obj.magic
                          (Pulse_RuntimeUtils.with_context
                             (Pulse_Typing_Env.get_context g)
                             (fun uu___ ->
                                FStar_Tactics_V2_Builtins.try_unify
                                  (Pulse_Typing.elab_env g) uvs1
                                  (Pulse_Elaborate_Pure.elab_term p)
                                  (Pulse_Elaborate_Pure.elab_term q))))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | (l, issues) ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.Match.fst"
                                               (Prims.of_int (236))
                                               (Prims.of_int (2))
                                               (Prims.of_int (236))
                                               (Prims.of_int (21)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.Match.fst"
                                               (Prims.of_int (241))
                                               (Prims.of_int (2))
                                               (Prims.of_int (257))
                                               (Prims.of_int (10)))))
                                      (Obj.magic
                                         (FStar_Tactics_V2_Builtins.log_issues
                                            issues))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              match l with
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  Pulse_Checker_Prover_Substs.empty
                                              | FStar_Pervasives_Native.Some
                                                  l1 ->
                                                  FStar_List_Tot_Base.fold_left
                                                    (fun ss ->
                                                       fun uu___3 ->
                                                         match uu___3 with
                                                         | (x, t) ->
                                                             if
                                                               (FStar_Set.mem
                                                                  (FStar_Reflection_V2_Builtins.inspect_namedv
                                                                    x).FStar_Reflection_V2_Data.uniq
                                                                  (Pulse_Syntax_Naming.freevars
                                                                    q))
                                                                 &&
                                                                 (Prims.op_Negation
                                                                    (
                                                                    FStar_Set.mem
                                                                    (FStar_Reflection_V2_Builtins.inspect_namedv
                                                                    x).FStar_Reflection_V2_Data.uniq
                                                                    (Pulse_Checker_Prover_Substs.dom
                                                                    ss)))
                                                             then
                                                               Pulse_Checker_Prover_Substs.push
                                                                 ss
                                                                 (FStar_Reflection_V2_Builtins.inspect_namedv
                                                                    x).FStar_Reflection_V2_Data.uniq
                                                                 t
                                                             else ss)
                                                    Pulse_Checker_Prover_Substs.empty
                                                    l1)))) uu___))) uu___)
let (eq_tm_unascribe :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (unit, unit, unit) FStar_Reflection_Typing.equiv
          FStar_Pervasives_Native.option)
  =
  fun g ->
    fun p ->
      fun q ->
        let rec unascribe t =
          match FStar_Reflection_V2_Builtins.inspect_ln t with
          | FStar_Reflection_V2_Data.Tv_AscribedT (t1, uu___, uu___1, uu___2)
              -> unascribe t1
          | FStar_Reflection_V2_Data.Tv_AscribedC (t1, uu___, uu___1, uu___2)
              -> unascribe t1
          | uu___ -> t in
        if Pulse_Syntax_Base.eq_tm (unascribe p) (unascribe q)
        then
          FStar_Pervasives_Native.Some
            (FStar_Reflection_Typing.Rel_eq_token
               ((Pulse_Typing.elab_env g),
                 (Pulse_Elaborate_Pure.elab_term p),
                 (Pulse_Elaborate_Pure.elab_term q), ()))
        else FStar_Pervasives_Native.None
let (unify :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          ((Pulse_Checker_Prover_Substs.ss_t,
             (unit, unit, unit) FStar_Reflection_Typing.equiv
               FStar_Pervasives_Native.option)
             Prims.dtuple2,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun p ->
        fun q ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                     (Prims.of_int (283)) (Prims.of_int (11))
                     (Prims.of_int (283)) (Prims.of_int (36)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                     (Prims.of_int (283)) (Prims.of_int (39))
                     (Prims.of_int (297)) (Prims.of_int (23)))))
            (Obj.magic (try_solve_uvars g uvs p q))
            (fun uu___ ->
               (fun ss ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.fst"
                                (Prims.of_int (284)) (Prims.of_int (10))
                                (Prims.of_int (284)) (Prims.of_int (16)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.fst"
                                (Prims.of_int (284)) (Prims.of_int (19))
                                (Prims.of_int (297)) (Prims.of_int (23)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             Pulse_Checker_Prover_Base.op_Array_Access ss q))
                       (fun uu___ ->
                          (fun q1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Prover.Match.fst"
                                           (Prims.of_int (285))
                                           (Prims.of_int (14))
                                           (Prims.of_int (285))
                                           (Prims.of_int (35)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Prover.Match.fst"
                                           (Prims.of_int (286))
                                           (Prims.of_int (2))
                                           (Prims.of_int (297))
                                           (Prims.of_int (23)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ -> eq_tm_unascribe g p q1))
                                  (fun uu___ ->
                                     (fun is_eq ->
                                        match is_eq with
                                        | FStar_Pervasives_Native.Some eq ->
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___ ->
                                                       Prims.Mkdtuple2
                                                         (ss,
                                                           (FStar_Pervasives_Native.Some
                                                              eq)))))
                                        | FStar_Pervasives_Native.None ->
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.Match.fst"
                                                             (Prims.of_int (289))
                                                             (Prims.of_int (7))
                                                             (Prims.of_int (289))
                                                             (Prims.of_int (28)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.Match.fst"
                                                             (Prims.of_int (289))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (297))
                                                             (Prims.of_int (23)))))
                                                    (Obj.magic
                                                       (contains_uvar q1 uvs
                                                          g))
                                                    (fun uu___ ->
                                                       (fun uu___ ->
                                                          if uu___
                                                          then
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    Prims.Mkdtuple2
                                                                    (ss,
                                                                    FStar_Pervasives_Native.None))))
                                                          else
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (43)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (23)))))
                                                                    (
                                                                    Obj.magic
                                                                    (eligible_for_smt_equality
                                                                    g p q1))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    if uu___2
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Elaborate_Pure.elab_term
                                                                    p))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun v0
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Elaborate_Pure.elab_term
                                                                    q1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun v1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Util.check_equiv_now
                                                                    (Pulse_Typing.elab_env
                                                                    g) v0 v1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    token,
                                                                    uu___5)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (ss,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Reflection_Typing.Rel_eq_token
                                                                    ((Pulse_Typing.elab_env
                                                                    g), v0,
                                                                    v1, ()))))
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    uu___5)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (ss,
                                                                    FStar_Pervasives_Native.None)))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.Mkdtuple2
                                                                    (ss,
                                                                    FStar_Pervasives_Native.None)))))
                                                                    uu___2))))
                                                         uu___)))) uu___)))
                            uu___))) uu___)
let (try_match_pq :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop ->
          ((Pulse_Checker_Prover_Substs.ss_t,
             unit FStar_Pervasives_Native.option) Prims.dtuple2,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun p ->
        fun q ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                     (Prims.of_int (303)) (Prims.of_int (10))
                     (Prims.of_int (303)) (Prims.of_int (25)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                     (Prims.of_int (304)) (Prims.of_int (2))
                     (Prims.of_int (306)) (Prims.of_int (73)))))
            (Obj.magic (unify g uvs p q))
            (fun r ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    match r with
                    | Prims.Mkdtuple2 (ss, FStar_Pervasives_Native.None) ->
                        Prims.Mkdtuple2 (ss, FStar_Pervasives_Native.None)
                    | Prims.Mkdtuple2
                        (ss, FStar_Pervasives_Native.Some uu___1) ->
                        Prims.Mkdtuple2
                          (ss, (FStar_Pervasives_Native.Some ()))))
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (match_step :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop Prims.list ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop Prims.list ->
              unit ->
                (unit Pulse_Checker_Prover_Base.prover_state
                   FStar_Pervasives_Native.option,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      fun p ->
        fun remaining_ctxt' ->
          fun q ->
            fun unsolved' ->
              fun uu___ ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Match.fst"
                           (Prims.of_int (317)) (Prims.of_int (11))
                           (Prims.of_int (317)) (Prims.of_int (21)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Match.fst"
                           (Prims.of_int (318)) (Prims.of_int (52))
                           (Prims.of_int (382)) (Prims.of_int (11)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        Pulse_Checker_Prover_Base.op_Array_Access
                          pst.Pulse_Checker_Prover_Base.ss q))
                  (fun uu___1 ->
                     (fun q_ss ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.Match.fst"
                                      (Prims.of_int (320))
                                      (Prims.of_int (23))
                                      (Prims.of_int (320))
                                      (Prims.of_int (57)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.Match.fst"
                                      (Prims.of_int (318))
                                      (Prims.of_int (52))
                                      (Prims.of_int (382))
                                      (Prims.of_int (11)))))
                             (Obj.magic
                                (try_match_pq
                                   pst.Pulse_Checker_Prover_Base.pg
                                   pst.Pulse_Checker_Prover_Base.uvs p q_ss))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   match uu___1 with
                                   | Prims.Mkdtuple2 (ss_q, ropt) ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.Match.fst"
                                                     (Prims.of_int (322))
                                                     Prims.int_zero
                                                     (Prims.of_int (324))
                                                     (Prims.of_int (101)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.Match.fst"
                                                     (Prims.of_int (326))
                                                     Prims.int_zero
                                                     (Prims.of_int (382))
                                                     (Prims.of_int (11)))))
                                            (Obj.magic
                                               (Pulse_Checker_Prover_Util.debug_prover
                                                  pst.Pulse_Checker_Prover_Base.pg
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.Match.fst"
                                                                (Prims.of_int (323))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (324))
                                                                (Prims.of_int (100)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.Match.fst"
                                                                (Prims.of_int (323))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (324))
                                                                (Prims.of_int (100)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (57)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (100)))))
                                                             (Obj.magic
                                                                (Pulse_Syntax_Printer.term_to_string
                                                                   (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    ss_q q_ss)))
                                                             (fun uu___3 ->
                                                                (fun uu___3
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (100)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (100)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (24)))))
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
                                                                    p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "prover matcher: tried to match p "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " and q (partially substituted) "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", result: "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                  uu___3)))
                                                       (fun uu___3 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               uu___3
                                                                 (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    ropt
                                                                  then "fail"
                                                                  else
                                                                    "success"))))))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    match ropt with
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        FStar_Pervasives_Native.None
                                                    | FStar_Pervasives_Native.Some
                                                        veq ->
                                                        FStar_Pervasives_Native.Some
                                                          {
                                                            Pulse_Checker_Prover_Base.pg
                                                              =
                                                              (pst.Pulse_Checker_Prover_Base.pg);
                                                            Pulse_Checker_Prover_Base.remaining_ctxt
                                                              =
                                                              remaining_ctxt';
                                                            Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                              = ();
                                                            Pulse_Checker_Prover_Base.uvs
                                                              =
                                                              (pst.Pulse_Checker_Prover_Base.uvs);
                                                            Pulse_Checker_Prover_Base.ss
                                                              =
                                                              (Pulse_Checker_Prover_Substs.push_ss
                                                                 pst.Pulse_Checker_Prover_Base.ss
                                                                 ss_q);
                                                            Pulse_Checker_Prover_Base.nts
                                                              =
                                                              FStar_Pervasives_Native.None;
                                                            Pulse_Checker_Prover_Base.solved
                                                              =
                                                              (Pulse_Checker_Prover_Base.op_Star
                                                                 q
                                                                 pst.Pulse_Checker_Prover_Base.solved);
                                                            Pulse_Checker_Prover_Base.unsolved
                                                              = unsolved';
                                                            Pulse_Checker_Prover_Base.k
                                                              =
                                                              (coerce_eq
                                                                 (Pulse_Checker_Base.k_elab_equiv
                                                                    preamble.Pulse_Checker_Prover_Base.g0
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (
                                                                    Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (
                                                                    Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (
                                                                    Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    (p ::
                                                                    remaining_ctxt'))
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    (Pulse_Checker_Prover_Substs.push_ss
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    ss_q)
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (
                                                                    Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    remaining_ctxt')
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    (Pulse_Checker_Prover_Substs.push_ss
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    ss_q) q)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    (Pulse_Checker_Prover_Substs.push_ss
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    ss_q)
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    (
                                                                    coerce_eq
                                                                    pst.Pulse_Checker_Prover_Base.k
                                                                    ()) () ())
                                                                 ());
                                                            Pulse_Checker_Prover_Base.goals_inv
                                                              = ();
                                                            Pulse_Checker_Prover_Base.solved_inv
                                                              = ()
                                                          })))) uu___1)))
                       uu___1)
let (remaining_ctxt_equiv_pst :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.vprop Prims.list ->
        unit -> unit Pulse_Checker_Prover_Base.prover_state)
  =
  fun preamble ->
    fun pst ->
      fun remaining_ctxt' ->
        fun d ->
          {
            Pulse_Checker_Prover_Base.pg = (pst.Pulse_Checker_Prover_Base.pg);
            Pulse_Checker_Prover_Base.remaining_ctxt = remaining_ctxt';
            Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing = ();
            Pulse_Checker_Prover_Base.uvs =
              (pst.Pulse_Checker_Prover_Base.uvs);
            Pulse_Checker_Prover_Base.ss = (pst.Pulse_Checker_Prover_Base.ss);
            Pulse_Checker_Prover_Base.nts =
              (pst.Pulse_Checker_Prover_Base.nts);
            Pulse_Checker_Prover_Base.solved =
              (pst.Pulse_Checker_Prover_Base.solved);
            Pulse_Checker_Prover_Base.unsolved =
              (pst.Pulse_Checker_Prover_Base.unsolved);
            Pulse_Checker_Prover_Base.k =
              (Pulse_Checker_Base.k_elab_equiv
                 preamble.Pulse_Checker_Prover_Base.g0
                 (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__pg
                    preamble pst)
                 (Pulse_Checker_Prover_Base.op_Star
                    preamble.Pulse_Checker_Prover_Base.ctxt
                    preamble.Pulse_Checker_Prover_Base.frame)
                 (Pulse_Checker_Prover_Base.op_Star
                    preamble.Pulse_Checker_Prover_Base.ctxt
                    preamble.Pulse_Checker_Prover_Base.frame)
                 (Pulse_Checker_Prover_Base.op_Star
                    (Pulse_Checker_Prover_Base.op_Star
                       (Pulse_Typing_Combinators.list_as_vprop
                          (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__remaining_ctxt
                             preamble pst))
                       preamble.Pulse_Checker_Prover_Base.frame)
                    (Pulse_Checker_Prover_Base.op_Array_Access
                       (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__ss
                          preamble pst)
                       (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__solved
                          preamble pst)))
                 (Pulse_Checker_Prover_Base.op_Star
                    (Pulse_Checker_Prover_Base.op_Star
                       (Pulse_Typing_Combinators.list_as_vprop
                          remaining_ctxt')
                       preamble.Pulse_Checker_Prover_Base.frame)
                    (Pulse_Checker_Prover_Base.op_Array_Access
                       pst.Pulse_Checker_Prover_Base.ss
                       pst.Pulse_Checker_Prover_Base.solved))
                 pst.Pulse_Checker_Prover_Base.k () ());
            Pulse_Checker_Prover_Base.goals_inv = ();
            Pulse_Checker_Prover_Base.solved_inv = ()
          }
let rec (match_q_aux :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop Prims.list ->
          unit ->
            Prims.nat ->
              (unit Pulse_Checker_Prover_Base.prover_state
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun preamble ->
                 fun pst ->
                   fun q ->
                     fun unsolved' ->
                       fun uu___ ->
                         fun i ->
                           if
                             (FStar_List_Tot_Base.length
                                pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                               = Prims.int_zero
                           then
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        FStar_Pervasives_Native.None)))
                           else
                             Obj.magic
                               (Obj.repr
                                  (if
                                     i =
                                       (FStar_List_Tot_Base.length
                                          pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                   then
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 ->
                                             FStar_Pervasives_Native.None))
                                   else
                                     Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.Match.fst"
                                                   (Prims.of_int (405))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (405))
                                                   (Prims.of_int (35)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.Match.fst"
                                                   (Prims.of_int (405))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (414))
                                                   (Prims.of_int (42)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                FStar_List_Tot_Base.hd
                                                  pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                                          (fun uu___3 ->
                                             (fun p ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.Match.fst"
                                                              (Prims.of_int (407))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (407))
                                                              (Prims.of_int (63)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.Match.fst"
                                                              (Prims.of_int (408))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (414))
                                                              (Prims.of_int (42)))))
                                                     (Obj.magic
                                                        (match_step preamble
                                                           pst p
                                                           (FStar_List_Tot_Base.tl
                                                              pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                           q unsolved' ()))
                                                     (fun uu___3 ->
                                                        (fun pst_opt ->
                                                           match pst_opt with
                                                           | FStar_Pervasives_Native.Some
                                                               pst1 ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    pst1)))
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    remaining_ctxt_equiv_pst
                                                                    preamble
                                                                    pst
                                                                    (FStar_List_Tot_Base.append
                                                                    (FStar_List_Tot_Base.tl
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    [
                                                                    FStar_List_Tot_Base.hd
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt])
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun pst1
                                                                    ->
                                                                    Obj.magic
                                                                    (match_q_aux
                                                                    preamble
                                                                    pst1 q
                                                                    unsolved'
                                                                    ()
                                                                    (i +
                                                                    Prims.int_one)))
                                                                    uu___3))))
                                                          uu___3))) uu___3)))))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (has_structure : Pulse_Syntax_Base.vprop -> Prims.bool) =
  fun q ->
    match Pulse_Syntax_Pure.inspect_term q with
    | FStar_Pervasives_Native.Some (Pulse_Syntax_Pure.Tm_Star
        (uu___, uu___1)) -> true
    | uu___ -> false
let (match_q :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop Prims.list ->
          unit ->
            Pulse_Checker_Prover_Base.prover_t ->
              (unit Pulse_Checker_Prover_Base.prover_state
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      fun q ->
        fun unsolved' ->
          fun uu___ ->
            fun prover ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                         (Prims.of_int (428)) (Prims.of_int (11))
                         (Prims.of_int (428)) (Prims.of_int (21)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                         (Prims.of_int (430)) Prims.int_zero
                         (Prims.of_int (624)) (Prims.of_int (37)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      Pulse_Checker_Prover_Base.op_Array_Access
                        pst.Pulse_Checker_Prover_Base.ss q))
                (fun uu___1 ->
                   (fun q_ss ->
                      if has_structure q_ss
                      then
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.Match.fst"
                                      (Prims.of_int (433)) (Prims.of_int (4))
                                      (Prims.of_int (437))
                                      (Prims.of_int (45)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.Match.fst"
                                      (Prims.of_int (438)) (Prims.of_int (6))
                                      (Prims.of_int (622))
                                      (Prims.of_int (11)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   {
                                     Pulse_Checker_Prover_Base.g0 =
                                       (pst.Pulse_Checker_Prover_Base.pg);
                                     Pulse_Checker_Prover_Base.ctxt =
                                       (Pulse_Typing_Combinators.list_as_vprop
                                          pst.Pulse_Checker_Prover_Base.remaining_ctxt);
                                     Pulse_Checker_Prover_Base.frame =
                                       (Pulse_Checker_Prover_Base.op_Star
                                          preamble.Pulse_Checker_Prover_Base.frame
                                          (Pulse_Checker_Prover_Base.op_Array_Access
                                             pst.Pulse_Checker_Prover_Base.ss
                                             pst.Pulse_Checker_Prover_Base.solved));
                                     Pulse_Checker_Prover_Base.ctxt_frame_typing
                                       = ();
                                     Pulse_Checker_Prover_Base.goals =
                                       (Pulse_Checker_Prover_Base.op_Star
                                          q_ss
                                          (Pulse_Typing_Combinators.list_as_vprop
                                             unsolved'))
                                   }))
                             (fun uu___1 ->
                                (fun preamble_sub ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Match.fst"
                                                 (Prims.of_int (442))
                                                 (Prims.of_int (105))
                                                 (Prims.of_int (451))
                                                 (Prims.of_int (18)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Match.fst"
                                                 (Prims.of_int (453))
                                                 (Prims.of_int (37))
                                                 (Prims.of_int (622))
                                                 (Prims.of_int (11)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              coerce_eq
                                                (Pulse_Checker_Base.k_elab_equiv
                                                   preamble_sub.Pulse_Checker_Prover_Base.g0
                                                   preamble_sub.Pulse_Checker_Prover_Base.g0
                                                   (Pulse_Checker_Prover_Base.op_Star
                                                      preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                      preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                   (Pulse_Checker_Prover_Base.op_Star
                                                      preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                      preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                   (Pulse_Checker_Prover_Base.op_Star
                                                      preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                      preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                   (Pulse_Checker_Prover_Base.op_Star
                                                      (Pulse_Checker_Prover_Base.op_Star
                                                         (Pulse_Typing_Combinators.list_as_vprop
                                                            (Pulse_Typing_Combinators.vprop_as_list
                                                               preamble_sub.Pulse_Checker_Prover_Base.ctxt))
                                                         preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                      (Pulse_Checker_Prover_Base.op_Array_Access
                                                         pst.Pulse_Checker_Prover_Base.ss
                                                         Pulse_Syntax_Pure.tm_emp))
                                                   (Pulse_Checker_Base.k_elab_unit
                                                      preamble_sub.Pulse_Checker_Prover_Base.g0
                                                      (Pulse_Checker_Prover_Base.op_Star
                                                         preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                         preamble_sub.Pulse_Checker_Prover_Base.frame))
                                                   () ()) ()))
                                        (fun uu___1 ->
                                           (fun k_sub ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.Match.fst"
                                                            (Prims.of_int (455))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (465))
                                                            (Prims.of_int (20)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.Match.fst"
                                                            (Prims.of_int (466))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (622))
                                                            (Prims.of_int (11)))))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Checker_Prover_Base.pg
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.pg);
                                                           Pulse_Checker_Prover_Base.remaining_ctxt
                                                             =
                                                             (Pulse_Typing_Combinators.vprop_as_list
                                                                preamble_sub.Pulse_Checker_Prover_Base.ctxt);
                                                           Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                             = ();
                                                           Pulse_Checker_Prover_Base.uvs
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.uvs);
                                                           Pulse_Checker_Prover_Base.ss
                                                             =
                                                             (pst.Pulse_Checker_Prover_Base.ss);
                                                           Pulse_Checker_Prover_Base.nts
                                                             =
                                                             FStar_Pervasives_Native.None;
                                                           Pulse_Checker_Prover_Base.solved
                                                             =
                                                             Pulse_Syntax_Pure.tm_emp;
                                                           Pulse_Checker_Prover_Base.unsolved
                                                             =
                                                             (Pulse_Typing_Combinators.vprop_as_list
                                                                q_ss);
                                                           Pulse_Checker_Prover_Base.k
                                                             = k_sub;
                                                           Pulse_Checker_Prover_Base.goals_inv
                                                             = ();
                                                           Pulse_Checker_Prover_Base.solved_inv
                                                             = ()
                                                         }))
                                                   (fun uu___1 ->
                                                      (fun pst_sub ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (30)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (470))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (11)))))
                                                              (Obj.magic
                                                                 (prover
                                                                    preamble_sub
                                                                    pst_sub))
                                                              (fun uu___1 ->
                                                                 (fun
                                                                    pst_sub1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    pst_sub1.Pulse_Checker_Prover_Base.k))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Checker_Base.k_elab_equiv
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.frame
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.frame
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    pst_sub1.Pulse_Checker_Prover_Base.solved))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    pst_sub1.Pulse_Checker_Prover_Base.solved)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    k_sub1 ()
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    pst_sub_goals_inv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (11)))))
                                                                    (match 
                                                                    pst_sub1.Pulse_Checker_Prover_Base.nts
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    r)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Substs.ss_to_nt_substs
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    pst_sub1.Pulse_Checker_Prover_Base.uvs
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun r ->
                                                                    match r
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    msg ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    FStar_Pervasives_Native.None
                                                                    (Prims.strcat
                                                                    "resulted substitution after match protocol is not well-typed: "
                                                                    (Prims.strcat
                                                                    msg ""))))
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    nt ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    nt))))
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (nt,
                                                                    effect_labels)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Checker_Prover_Base.pg
                                                                    =
                                                                    (pst_sub1.Pulse_Checker_Prover_Base.pg);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt
                                                                    =
                                                                    (pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.uvs
                                                                    =
                                                                    (pst_sub1.Pulse_Checker_Prover_Base.uvs);
                                                                    Pulse_Checker_Prover_Base.ss
                                                                    =
                                                                    (pst_sub1.Pulse_Checker_Prover_Base.ss);
                                                                    Pulse_Checker_Prover_Base.nts
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (nt,
                                                                    effect_labels)));
                                                                    Pulse_Checker_Prover_Base.solved
                                                                    =
                                                                    (preamble.Pulse_Checker_Prover_Base.goals);
                                                                    Pulse_Checker_Prover_Base.unsolved
                                                                    = [];
                                                                    Pulse_Checker_Prover_Base.k
                                                                    =
                                                                    (Pulse_Checker_Base.k_elab_trans
                                                                    preamble.Pulse_Checker_Prover_Base.g0
                                                                    (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__pg
                                                                    preamble
                                                                    pst)
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__remaining_ctxt
                                                                    preamble
                                                                    pst))
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__ss
                                                                    preamble
                                                                    pst)
                                                                    (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__solved
                                                                    preamble
                                                                    pst)))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    preamble.Pulse_Checker_Prover_Base.goals))
                                                                    pst.Pulse_Checker_Prover_Base.k
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.unsolved)
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    preamble.Pulse_Checker_Prover_Base.goals))
                                                                    (coerce_eq
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    pst_sub1.Pulse_Checker_Prover_Base.solved)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.unsolved))
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    k_sub2 ()
                                                                    ()) ())
                                                                    () ()));
                                                                    Pulse_Checker_Prover_Base.goals_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.solved_inv
                                                                    = ()
                                                                    }))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                   uu___1)))
                                                        uu___1))) uu___1)))
                                  uu___1))
                      else
                        Obj.magic
                          (match_q_aux preamble pst q unsolved' ()
                             Prims.int_zero)) uu___1)