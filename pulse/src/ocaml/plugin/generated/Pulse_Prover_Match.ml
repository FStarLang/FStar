open Prims
let (equational : Pulse_Syntax_Base.term -> Prims.bool) =
  fun t ->
    match t.Pulse_Syntax_Base.t with
    | Pulse_Syntax_Base.Tm_FStar host_term ->
        (match FStar_Reflection_V2_Builtins.inspect_ln host_term with
         | FStar_Reflection_V2_Data.Tv_Match (uu___, uu___1, uu___2) -> true
         | uu___ -> false)
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
        name = ["Steel"; "Effect"; "Common"; "smt_fallback"]
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
                (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                   (Prims.of_int (87)) (Prims.of_int (31))
                   (Prims.of_int (87)) (Prims.of_int (61)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                   (Prims.of_int (87)) (Prims.of_int (64))
                   (Prims.of_int (145)) (Prims.of_int (31)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> fun uu___1 -> (equational t0) || (equational t1)))
          (fun uu___ ->
             (fun either_equational ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                              (Prims.of_int (89)) (Prims.of_int (6))
                              (Prims.of_int (92)) (Prims.of_int (18)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                              (Prims.of_int (94)) (Prims.of_int (4))
                              (Prims.of_int (145)) (Prims.of_int (31)))))
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
                           match ((t0.Pulse_Syntax_Base.t),
                                   (t1.Pulse_Syntax_Base.t))
                           with
                           | (Pulse_Syntax_Base.Tm_FStar t01,
                              Pulse_Syntax_Base.Tm_FStar t11) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Prover.Match.fst"
                                                (Prims.of_int (96))
                                                (Prims.of_int (22))
                                                (Prims.of_int (96))
                                                (Prims.of_int (41)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Prover.Match.fst"
                                                (Prims.of_int (95))
                                                (Prims.of_int (34))
                                                (Prims.of_int (144))
                                                (Prims.of_int (5)))))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___ ->
                                             FStar_Reflection_V2_Derived.collect_app_ln
                                               t01))
                                       (fun uu___ ->
                                          (fun uu___ ->
                                             match uu___ with
                                             | (h0, args0) ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Prover.Match.fst"
                                                               (Prims.of_int (97))
                                                               (Prims.of_int (22))
                                                               (Prims.of_int (97))
                                                               (Prims.of_int (41)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Prover.Match.fst"
                                                               (Prims.of_int (96))
                                                               (Prims.of_int (44))
                                                               (Prims.of_int (143))
                                                               (Prims.of_int (31)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___1 ->
                                                            FStar_Reflection_V2_Derived.collect_app_ln
                                                              t11))
                                                      (fun uu___1 ->
                                                         (fun uu___1 ->
                                                            match uu___1 with
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
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (type_of_fv
                                                                    g fv))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
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
                                                                    uu___4)
                                                                    ->
                                                                    (match 
                                                                    FStar_List_Tot_Base.fold_right
                                                                    (fun b ->
                                                                    fun
                                                                    uu___5 ->
                                                                    match uu___5
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
                                                                    t01 t11
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
                                                                    uu___6)::args02,
                                                                    (a1,
                                                                    uu___7)::args12,
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
                                                                    uu___6 ->
                                                                    either_equational
                                                                    () in
                                                                    aux args0
                                                                    args1
                                                                    fallbacks))))))
                                                                    | 
                                                                    FStar_Reflection_V2_Data.Tv_UInst
                                                                    (fv,
                                                                    uu___2)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (140))
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
                                                                    t01 t11
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
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    either_equational
                                                                    ()))))
                                                                else
                                                                  Obj.magic
                                                                    (
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    either_equational
                                                                    ()))))
                                                           uu___1))) uu___)))
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
let rec (refl_contains_uvar :
  FStar_Reflection_Types.term ->
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
               match FStar_Reflection_V2_Builtins.inspect_ln t with
               | FStar_Reflection_V2_Data.Tv_Var uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              FStar_Pervasives_Native.uu___is_Some
                                (refl_uvar t uvs))))
               | FStar_Reflection_V2_Data.Tv_BVar uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> false)))
               | FStar_Reflection_V2_Data.Tv_FVar uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> false)))
               | FStar_Reflection_V2_Data.Tv_UInst (uu___, uu___1) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___2 -> false)))
               | FStar_Reflection_V2_Data.Tv_Const uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> false)))
               | FStar_Reflection_V2_Data.Tv_Type uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> false)))
               | FStar_Reflection_V2_Data.Tv_App (hd, (arg, uu___)) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Match.fst"
                                    (Prims.of_int (166)) (Prims.of_int (12))
                                    (Prims.of_int (166)) (Prims.of_int (39)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Match.fst"
                                    (Prims.of_int (167)) (Prims.of_int (4))
                                    (Prims.of_int (168)) (Prims.of_int (37)))))
                           (Obj.magic (refl_contains_uvar hd uvs g))
                           (fun uu___1 ->
                              (fun b ->
                                 if b
                                 then
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 -> true)))
                                 else
                                   Obj.magic
                                     (Obj.repr (refl_contains_uvar arg uvs g)))
                                uu___1)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (Pulse_Typing_Env.fail g FStar_Pervasives_Native.None
                           "refl_contains_uvar: unsupported reflection term")))
          uu___2 uu___1 uu___
let (is_uvar :
  Pulse_Syntax_Base.term ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.var FStar_Pervasives_Native.option)
  =
  fun t ->
    fun uvs ->
      match t.Pulse_Syntax_Base.t with
      | Pulse_Syntax_Base.Tm_FStar t1 -> refl_uvar t1 uvs
      | uu___ -> FStar_Pervasives_Native.None
let rec (contains_uvar :
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
               match t.Pulse_Syntax_Base.t with
               | Pulse_Syntax_Base.Tm_Emp ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> false)))
               | Pulse_Syntax_Base.Tm_Pure p ->
                   Obj.magic (Obj.repr (contains_uvar p uvs g))
               | Pulse_Syntax_Base.Tm_Star (t1, t2) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Match.fst"
                                    (Prims.of_int (183)) (Prims.of_int (12))
                                    (Prims.of_int (183)) (Prims.of_int (34)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Match.fst"
                                    (Prims.of_int (184)) (Prims.of_int (4))
                                    (Prims.of_int (185)) (Prims.of_int (31)))))
                           (Obj.magic (contains_uvar t1 uvs g))
                           (fun uu___ ->
                              (fun b ->
                                 if b
                                 then
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___ -> true)))
                                 else
                                   Obj.magic
                                     (Obj.repr (contains_uvar t2 uvs g)))
                                uu___)))
               | Pulse_Syntax_Base.Tm_ExistsSL
                   (uu___,
                    { Pulse_Syntax_Base.binder_ty = t1;
                      Pulse_Syntax_Base.binder_ppname = uu___1;_},
                    t2)
                   ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Match.fst"
                                    (Prims.of_int (183)) (Prims.of_int (12))
                                    (Prims.of_int (183)) (Prims.of_int (34)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Match.fst"
                                    (Prims.of_int (184)) (Prims.of_int (4))
                                    (Prims.of_int (185)) (Prims.of_int (31)))))
                           (Obj.magic (contains_uvar t1 uvs g))
                           (fun uu___2 ->
                              (fun b ->
                                 if b
                                 then
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 -> true)))
                                 else
                                   Obj.magic
                                     (Obj.repr (contains_uvar t2 uvs g)))
                                uu___2)))
               | Pulse_Syntax_Base.Tm_ForallSL
                   (uu___,
                    { Pulse_Syntax_Base.binder_ty = t1;
                      Pulse_Syntax_Base.binder_ppname = uu___1;_},
                    t2)
                   ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Match.fst"
                                    (Prims.of_int (183)) (Prims.of_int (12))
                                    (Prims.of_int (183)) (Prims.of_int (34)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Match.fst"
                                    (Prims.of_int (184)) (Prims.of_int (4))
                                    (Prims.of_int (185)) (Prims.of_int (31)))))
                           (Obj.magic (contains_uvar t1 uvs g))
                           (fun uu___2 ->
                              (fun b ->
                                 if b
                                 then
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 -> true)))
                                 else
                                   Obj.magic
                                     (Obj.repr (contains_uvar t2 uvs g)))
                                uu___2)))
               | Pulse_Syntax_Base.Tm_VProp ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> false)))
               | Pulse_Syntax_Base.Tm_Inames ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> false)))
               | Pulse_Syntax_Base.Tm_EmpInames ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> false)))
               | Pulse_Syntax_Base.Tm_FStar t1 ->
                   Obj.magic (Obj.repr (refl_contains_uvar t1 uvs g))
               | Pulse_Syntax_Base.Tm_Unknown ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> false)))) uu___2 uu___1 uu___
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
let rec (unify :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          unit ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.term ->
                unit ->
                  Pulse_Prover_Substs.ss_t ->
                    ((Pulse_Prover_Substs.ss_t,
                       (unit, unit, unit) FStar_Reflection_Typing.equiv)
                       Prims.dtuple2 FStar_Pervasives_Native.option,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun p ->
        fun p_t ->
          fun p_typing ->
            fun q ->
              fun q_t ->
                fun q_typing ->
                  fun ss ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                               (Prims.of_int (228)) (Prims.of_int (11))
                               (Prims.of_int (228)) (Prims.of_int (12)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                               (Prims.of_int (228)) (Prims.of_int (15))
                               (Prims.of_int (328)) (Prims.of_int (27)))))
                      (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> q))
                      (fun uu___ ->
                         (fun q0 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Match.fst"
                                          (Prims.of_int (229))
                                          (Prims.of_int (10))
                                          (Prims.of_int (229))
                                          (Prims.of_int (16)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Match.fst"
                                          (Prims.of_int (234))
                                          (Prims.of_int (2))
                                          (Prims.of_int (328))
                                          (Prims.of_int (27)))))
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ ->
                                       Pulse_Prover_Common.op_Array_Access ss
                                         q))
                                 (fun uu___ ->
                                    (fun q1 ->
                                       if Pulse_Syntax_Base.eq_tm p q1
                                       then
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___ ->
                                                    FStar_Pervasives_Native.Some
                                                      (Prims.Mkdtuple2
                                                         (ss,
                                                           (FStar_Reflection_Typing.EQ_Refl
                                                              ((Pulse_Typing.elab_env
                                                                  g),
                                                                (Pulse_Elaborate_Pure.elab_term
                                                                   p))))))))
                                       else
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Prover.Match.fst"
                                                          (Prims.of_int (239))
                                                          (Prims.of_int (10))
                                                          (Prims.of_int (239))
                                                          (Prims.of_int (37)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Prover.Match.fst"
                                                          (Prims.of_int (239))
                                                          (Prims.of_int (7))
                                                          (Prims.of_int (328))
                                                          (Prims.of_int (27)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Prover.Match.fst"
                                                                (Prims.of_int (239))
                                                                (Prims.of_int (14))
                                                                (Prims.of_int (239))
                                                                (Prims.of_int (37)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Prover.Match.fst"
                                                                (Prims.of_int (239))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (239))
                                                                (Prims.of_int (37)))))
                                                       (Obj.magic
                                                          (contains_uvar q1
                                                             uvs g))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               Prims.op_Negation
                                                                 uu___1))))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       if uu___1
                                                       then
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (38)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (13)))))
                                                                 (Obj.magic
                                                                    (
                                                                    eligible_for_smt_equality
                                                                    g p q1))
                                                                 (fun uu___2
                                                                    ->
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
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (26)))))
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
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (26)))))
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
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.check_equiv
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
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (ss,
                                                                    (FStar_Reflection_Typing.EQ_Token
                                                                    ((Pulse_Typing.elab_env
                                                                    g), v0,
                                                                    v1, ()))))
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    uu___5)
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___2)))
                                                       else
                                                         Obj.magic
                                                           (Obj.repr
                                                              (match 
                                                                 ((is_reveal_uvar
                                                                    q1 uvs),
                                                                   (is_reveal
                                                                    p))
                                                               with
                                                               | (FStar_Pervasives_Native.Some
                                                                  (u, ty, n),
                                                                  false) ->
                                                                   Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.mk_hide
                                                                    u ty p))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun w ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Prover_Substs.push
                                                                    uvs
                                                                    Pulse_Prover_Substs.empty
                                                                    n w))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    ss_new ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Prover_Substs.push_ss
                                                                    uvs ss
                                                                    ss_new))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun ss'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.check_equiv
                                                                    (Pulse_Typing.elab_env
                                                                    g)
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    (Pulse_Typing.mk_reveal
                                                                    u ty w))
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    p)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (b,
                                                                    uu___5)
                                                                    ->
                                                                    if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    b
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (ss',
                                                                    (Prims.magic
                                                                    ())))
                                                                    else
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3))
                                                               | uu___3 ->
                                                                   Obj.repr
                                                                    (match 
                                                                    is_uvar
                                                                    q1 uvs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    n ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    ((Pulse_Prover_Substs.push_ss
                                                                    uvs ss
                                                                    (Pulse_Prover_Substs.push
                                                                    uvs
                                                                    Pulse_Prover_Substs.empty
                                                                    n p)),
                                                                    (FStar_Reflection_Typing.EQ_Refl
                                                                    ((Pulse_Typing.elab_env
                                                                    g),
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    p)))))))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.repr
                                                                    (match 
                                                                    ((p.Pulse_Syntax_Base.t),
                                                                    (q1.Pulse_Syntax_Base.t))
                                                                    with
                                                                    | 
                                                                    (Pulse_Syntax_Base.Tm_Pure
                                                                    p1,
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    q11) ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    (unify g
                                                                    uvs p1
                                                                    (Prims.magic
                                                                    ()) ()
                                                                    q11
                                                                    (Prims.magic
                                                                    ()) () ss))
                                                                    (fun r ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match r
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (ss',
                                                                    uu___6))
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (ss',
                                                                    (Prims.magic
                                                                    ())))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    (uu___5,
                                                                    uu___6)
                                                                    ->
                                                                    Obj.repr
                                                                    (match 
                                                                    ((Pulse_Syntax_Pure.is_pure_app
                                                                    p),
                                                                    (Pulse_Syntax_Pure.is_pure_app
                                                                    q1))
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    (head_p,
                                                                    qual_p,
                                                                    arg_p),
                                                                    FStar_Pervasives_Native.Some
                                                                    (head_q,
                                                                    qual_q,
                                                                    arg_q))
                                                                    ->
                                                                    Obj.repr
                                                                    (if
                                                                    Prims.op_Negation
                                                                    (qual_p =
                                                                    qual_q)
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.None))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (unify g
                                                                    uvs
                                                                    head_p
                                                                    (Prims.magic
                                                                    ()) ()
                                                                    head_q
                                                                    (Prims.magic
                                                                    ()) () ss))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun r ->
                                                                    match r
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (ss',
                                                                    uu___8))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Match.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (unify g
                                                                    uvs arg_p
                                                                    (Prims.magic
                                                                    ()) ()
                                                                    arg_q
                                                                    (Prims.magic
                                                                    ()) ()
                                                                    ss'))
                                                                    (fun r1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match r1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (ss'1,
                                                                    uu___10))
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (ss'1,
                                                                    (Prims.magic
                                                                    ())))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    | 
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___8)))
                                                                    | 
                                                                    (uu___7,
                                                                    uu___8)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives_Native.None))))))))
                                                      uu___1)))) uu___)))
                           uu___)
let (try_match_pq :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.vprop ->
        unit ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              ((Pulse_Prover_Substs.ss_t, unit) Prims.dtuple2
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun p ->
        fun p_typing ->
          fun q ->
            fun q_typing ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                         (Prims.of_int (338)) (Prims.of_int (10))
                         (Prims.of_int (338)) (Prims.of_int (48)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                         (Prims.of_int (339)) (Prims.of_int (2))
                         (Prims.of_int (344)) (Prims.of_int (27)))))
                (Obj.magic
                   (unify g uvs p Pulse_Syntax_Base.tm_vprop () q
                      Pulse_Syntax_Base.tm_vprop () Pulse_Prover_Substs.empty))
                (fun r ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        match r with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some (Prims.Mkdtuple2
                            (ss, uu___1)) ->
                            FStar_Pervasives_Native.Some
                              (Prims.Mkdtuple2 (ss, ()))))
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (match_step :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop Prims.list ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop Prims.list ->
              unit ->
                (unit Pulse_Prover_Common.prover_state
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
                        (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                           (Prims.of_int (355)) (Prims.of_int (11))
                           (Prims.of_int (355)) (Prims.of_int (21)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                           (Prims.of_int (356)) (Prims.of_int (52))
                           (Prims.of_int (417)) (Prims.of_int (11)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        Pulse_Prover_Common.op_Array_Access
                          pst.Pulse_Prover_Common.ss q))
                  (fun uu___1 ->
                     (fun q_ss ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Prover.Match.fst"
                                      (Prims.of_int (358))
                                      (Prims.of_int (11))
                                      (Prims.of_int (358))
                                      (Prims.of_int (69)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Prover.Match.fst"
                                      (Prims.of_int (359)) Prims.int_zero
                                      (Prims.of_int (417))
                                      (Prims.of_int (11)))))
                             (Obj.magic
                                (try_match_pq pst.Pulse_Prover_Common.pg
                                   pst.Pulse_Prover_Common.uvs p () q_ss ()))
                             (fun ropt ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     match ropt with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some
                                         (Prims.Mkdtuple2 (ss_q, veq)) ->
                                         FStar_Pervasives_Native.Some
                                           {
                                             Pulse_Prover_Common.pg =
                                               (pst.Pulse_Prover_Common.pg);
                                             Pulse_Prover_Common.remaining_ctxt
                                               = remaining_ctxt';
                                             Pulse_Prover_Common.remaining_ctxt_frame_typing
                                               = ();
                                             Pulse_Prover_Common.uvs =
                                               (pst.Pulse_Prover_Common.uvs);
                                             Pulse_Prover_Common.ss =
                                               (Pulse_Prover_Substs.push_ss
                                                  pst.Pulse_Prover_Common.uvs
                                                  pst.Pulse_Prover_Common.ss
                                                  ss_q);
                                             Pulse_Prover_Common.solved =
                                               (Pulse_Prover_Common.op_Star q
                                                  pst.Pulse_Prover_Common.solved);
                                             Pulse_Prover_Common.unsolved =
                                               unsolved';
                                             Pulse_Prover_Common.solved_typing
                                               = ();
                                             Pulse_Prover_Common.k =
                                               (coerce_eq
                                                  (Pulse_Prover_Common.k_elab_equiv
                                                     preamble.Pulse_Prover_Common.g0
                                                     pst.Pulse_Prover_Common.pg
                                                     (Pulse_Prover_Common.op_Star
                                                        preamble.Pulse_Prover_Common.ctxt
                                                        preamble.Pulse_Prover_Common.frame)
                                                     (Pulse_Prover_Common.op_Star
                                                        preamble.Pulse_Prover_Common.ctxt
                                                        preamble.Pulse_Prover_Common.frame)
                                                     (Pulse_Prover_Common.op_Star
                                                        (Pulse_Prover_Common.op_Star
                                                           (Pulse_Checker_VPropEquiv.list_as_vprop
                                                              (p ::
                                                              remaining_ctxt'))
                                                           preamble.Pulse_Prover_Common.frame)
                                                        (Pulse_Prover_Common.op_Array_Access
                                                           (Pulse_Prover_Substs.push_ss
                                                              pst.Pulse_Prover_Common.uvs
                                                              pst.Pulse_Prover_Common.ss
                                                              ss_q)
                                                           pst.Pulse_Prover_Common.solved))
                                                     (Pulse_Prover_Common.op_Star
                                                        (Pulse_Prover_Common.op_Star
                                                           (Pulse_Checker_VPropEquiv.list_as_vprop
                                                              remaining_ctxt')
                                                           preamble.Pulse_Prover_Common.frame)
                                                        (Pulse_Prover_Common.op_Star
                                                           (Pulse_Prover_Common.op_Array_Access
                                                              (Pulse_Prover_Substs.push_ss
                                                                 pst.Pulse_Prover_Common.uvs
                                                                 pst.Pulse_Prover_Common.ss
                                                                 ss_q) q)
                                                           (Pulse_Prover_Common.op_Array_Access
                                                              (Pulse_Prover_Substs.push_ss
                                                                 pst.Pulse_Prover_Common.uvs
                                                                 pst.Pulse_Prover_Common.ss
                                                                 ss_q)
                                                              pst.Pulse_Prover_Common.solved)))
                                                     (coerce_eq
                                                        pst.Pulse_Prover_Common.k
                                                        ()) () ()) ());
                                             Pulse_Prover_Common.goals_inv =
                                               ()
                                           })))) uu___1)