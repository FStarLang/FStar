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
                (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                   (Prims.of_int (90)) (Prims.of_int (31))
                   (Prims.of_int (90)) (Prims.of_int (61)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                   (Prims.of_int (90)) (Prims.of_int (64))
                   (Prims.of_int (148)) (Prims.of_int (31)))))
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
                              (Prims.of_int (92)) (Prims.of_int (6))
                              (Prims.of_int (95)) (Prims.of_int (18)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.Match.fst"
                              (Prims.of_int (97)) (Prims.of_int (4))
                              (Prims.of_int (148)) (Prims.of_int (31)))))
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
                                                "Pulse.Checker.Prover.Match.fst"
                                                (Prims.of_int (99))
                                                (Prims.of_int (22))
                                                (Prims.of_int (99))
                                                (Prims.of_int (41)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Prover.Match.fst"
                                                (Prims.of_int (98))
                                                (Prims.of_int (34))
                                                (Prims.of_int (147))
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
                                                               "Pulse.Checker.Prover.Match.fst"
                                                               (Prims.of_int (100))
                                                               (Prims.of_int (22))
                                                               (Prims.of_int (100))
                                                               (Prims.of_int (41)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Prover.Match.fst"
                                                               (Prims.of_int (99))
                                                               (Prims.of_int (44))
                                                               (Prims.of_int (146))
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
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (143))
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
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (143))
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
let rec (try_solve_uvars :
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
                     (Prims.of_int (201)) (Prims.of_int (5))
                     (Prims.of_int (201)) (Prims.of_int (32)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                     (Prims.of_int (201)) (Prims.of_int (2))
                     (Prims.of_int (239)) (Prims.of_int (5)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Match.fst"
                           (Prims.of_int (201)) (Prims.of_int (9))
                           (Prims.of_int (201)) (Prims.of_int (32)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Match.fst"
                           (Prims.of_int (201)) (Prims.of_int (5))
                           (Prims.of_int (201)) (Prims.of_int (32)))))
                  (Obj.magic (contains_uvar q uvs g))
                  (fun uu___ ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> Prims.op_Negation uu___))))
            (fun uu___ ->
               (fun uu___ ->
                  if uu___
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> Pulse_Checker_Prover_Substs.empty)))
                  else
                    Obj.magic
                      (Obj.repr
                         (match ((is_reveal_uvar q uvs), (is_reveal p)) with
                          | (FStar_Pervasives_Native.Some (u, ty, n), false)
                              ->
                              Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      Pulse_Checker_Prover_Substs.push
                                        Pulse_Checker_Prover_Substs.empty n
                                        (Pulse_Typing.mk_hide u ty p)))
                          | uu___2 ->
                              Obj.repr
                                (match is_uvar q uvs with
                                 | FStar_Pervasives_Native.Some n ->
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 ->
                                             Pulse_Checker_Prover_Substs.push
                                               Pulse_Checker_Prover_Substs.empty
                                               n p))
                                 | uu___3 ->
                                     Obj.repr
                                       (match ((p.Pulse_Syntax_Base.t),
                                                (q.Pulse_Syntax_Base.t))
                                        with
                                        | (Pulse_Syntax_Base.Tm_Pure p1,
                                           Pulse_Syntax_Base.Tm_Pure q1) ->
                                            Obj.repr
                                              (try_solve_uvars g uvs p1 q1)
                                        | (uu___4, uu___5) ->
                                            Obj.repr
                                              (match ((Pulse_Syntax_Pure.is_pure_app
                                                         p),
                                                       (Pulse_Syntax_Pure.is_pure_app
                                                          q))
                                               with
                                               | (FStar_Pervasives_Native.Some
                                                  (head_p, qual_p, arg_p),
                                                  FStar_Pervasives_Native.Some
                                                  (head_q, qual_q, arg_q)) ->
                                                   Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Prover.Match.fst"
                                                                 (Prims.of_int (228))
                                                                 (Prims.of_int (26))
                                                                 (Prims.of_int (228))
                                                                 (Prims.of_int (61)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Prover.Match.fst"
                                                                 (Prims.of_int (228))
                                                                 (Prims.of_int (64))
                                                                 (Prims.of_int (237))
                                                                 (Prims.of_int (25)))))
                                                        (Obj.magic
                                                           (try_solve_uvars g
                                                              uvs head_p
                                                              head_q))
                                                        (fun uu___6 ->
                                                           (fun ss_head ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (58)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (25)))))
                                                                   (Obj.magic
                                                                    (try_solve_uvars
                                                                    g uvs
                                                                    arg_p
                                                                    arg_q))
                                                                   (fun
                                                                    ss_arg ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    if
                                                                    Pulse_Checker_Prover_Substs.check_disjoint
                                                                    ss_head
                                                                    ss_arg
                                                                    then
                                                                    Pulse_Checker_Prover_Substs.push_ss
                                                                    ss_head
                                                                    ss_arg
                                                                    else
                                                                    Pulse_Checker_Prover_Substs.empty))))
                                                             uu___6))
                                               | (uu___6, uu___7) ->
                                                   Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___8 ->
                                                           Pulse_Checker_Prover_Substs.empty))))))))
                 uu___)
let (unify :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          ((Pulse_Checker_Prover_Substs.ss_t,
             (unit, unit, unit) FStar_Reflection_Typing.equiv) Prims.dtuple2
             FStar_Pervasives_Native.option,
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
                     (Prims.of_int (256)) (Prims.of_int (11))
                     (Prims.of_int (256)) (Prims.of_int (36)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                     (Prims.of_int (256)) (Prims.of_int (39))
                     (Prims.of_int (268)) (Prims.of_int (11)))))
            (Obj.magic (try_solve_uvars g uvs p q))
            (fun uu___ ->
               (fun ss ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.fst"
                                (Prims.of_int (257)) (Prims.of_int (10))
                                (Prims.of_int (257)) (Prims.of_int (16)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.fst"
                                (Prims.of_int (258)) (Prims.of_int (2))
                                (Prims.of_int (268)) (Prims.of_int (11)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             Pulse_Checker_Prover_Base.op_Array_Access ss q))
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
                                                    ((Pulse_Typing.elab_env g),
                                                      (Pulse_Elaborate_Pure.elab_term
                                                         p))))))))
                             else
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Prover.Match.fst"
                                                (Prims.of_int (260))
                                                (Prims.of_int (10))
                                                (Prims.of_int (260))
                                                (Prims.of_int (31)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Prover.Match.fst"
                                                (Prims.of_int (260))
                                                (Prims.of_int (7))
                                                (Prims.of_int (268))
                                                (Prims.of_int (11)))))
                                       (Obj.magic (contains_uvar q1 uvs g))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             if uu___1
                                             then
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          FStar_Pervasives_Native.None)))
                                             else
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.Match.fst"
                                                                (Prims.of_int (262))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (262))
                                                                (Prims.of_int (41)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.Match.fst"
                                                                (Prims.of_int (262))
                                                                (Prims.of_int (7))
                                                                (Prims.of_int (268))
                                                                (Prims.of_int (11)))))
                                                       (Obj.magic
                                                          (eligible_for_smt_equality
                                                             g p q1))
                                                       (fun uu___3 ->
                                                          (fun uu___3 ->
                                                             if uu___3
                                                             then
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Elaborate_Pure.elab_term
                                                                    p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun v0
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Elaborate_Pure.elab_term
                                                                    q1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun v1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.check_equiv
                                                                    (Pulse_Typing.elab_env
                                                                    g) v0 v1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    token,
                                                                    uu___6)
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
                                                                    uu___6)
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                             else
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.None))))
                                                            uu___3)))) uu___1))))
                            uu___))) uu___)
let (try_match_pq :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop ->
          ((Pulse_Checker_Prover_Substs.ss_t, unit) Prims.dtuple2
             FStar_Pervasives_Native.option,
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
                     (Prims.of_int (387)) (Prims.of_int (10))
                     (Prims.of_int (387)) (Prims.of_int (25)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.fst"
                     (Prims.of_int (388)) (Prims.of_int (2))
                     (Prims.of_int (392)) (Prims.of_int (27)))))
            (Obj.magic (unify g uvs p q))
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
                           (Prims.of_int (403)) (Prims.of_int (11))
                           (Prims.of_int (403)) (Prims.of_int (21)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Match.fst"
                           (Prims.of_int (404)) (Prims.of_int (52))
                           (Prims.of_int (467)) (Prims.of_int (11)))))
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
                                      (Prims.of_int (406))
                                      (Prims.of_int (11))
                                      (Prims.of_int (406))
                                      (Prims.of_int (45)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.Match.fst"
                                      (Prims.of_int (408)) Prims.int_zero
                                      (Prims.of_int (467))
                                      (Prims.of_int (11)))))
                             (Obj.magic
                                (try_match_pq
                                   pst.Pulse_Checker_Prover_Base.pg
                                   pst.Pulse_Checker_Prover_Base.uvs p q_ss))
                             (fun uu___1 ->
                                (fun ropt ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Match.fst"
                                                 (Prims.of_int (408))
                                                 Prims.int_zero
                                                 (Prims.of_int (410))
                                                 (Prims.of_int (92)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Match.fst"
                                                 (Prims.of_int (412))
                                                 Prims.int_zero
                                                 (Prims.of_int (467))
                                                 (Prims.of_int (11)))))
                                        (Obj.magic
                                           (Pulse_Checker_Prover_Util.debug_prover
                                              pst.Pulse_Checker_Prover_Base.pg
                                              (fun uu___1 ->
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.Match.fst"
                                                            (Prims.of_int (409))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (410))
                                                            (Prims.of_int (91)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.Match.fst"
                                                            (Prims.of_int (409))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (410))
                                                            (Prims.of_int (91)))))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Prover.Match.fst"
                                                                  (Prims.of_int (410))
                                                                  (Prims.of_int (25))
                                                                  (Prims.of_int (410))
                                                                  (Prims.of_int (48)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Prover.Match.fst"
                                                                  (Prims.of_int (409))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (410))
                                                                  (Prims.of_int (91)))))
                                                         (Obj.magic
                                                            (Pulse_Syntax_Printer.term_to_string
                                                               q_ss))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (91)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (91)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (24)))))
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
                                                                    p))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "prover matcher: tried to match "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", result: "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                              uu___2)))
                                                   (fun uu___2 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 ->
                                                           uu___2
                                                             (if
                                                                FStar_Pervasives_Native.uu___is_None
                                                                  ropt
                                                              then "fail"
                                                              else "success"))))))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                match ropt with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    (Prims.Mkdtuple2
                                                    (ss_q, veq)) ->
                                                    FStar_Pervasives_Native.Some
                                                      {
                                                        Pulse_Checker_Prover_Base.pg
                                                          =
                                                          (pst.Pulse_Checker_Prover_Base.pg);
                                                        Pulse_Checker_Prover_Base.remaining_ctxt
                                                          = remaining_ctxt';
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
                                                                (Pulse_Checker_Prover_Base.op_Star
                                                                   preamble.Pulse_Checker_Prover_Base.ctxt
                                                                   preamble.Pulse_Checker_Prover_Base.frame)
                                                                (Pulse_Checker_Prover_Base.op_Star
                                                                   preamble.Pulse_Checker_Prover_Base.ctxt
                                                                   preamble.Pulse_Checker_Prover_Base.frame)
                                                                (Pulse_Checker_Prover_Base.op_Star
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
                                                                (Pulse_Checker_Prover_Base.op_Star
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
                                                                (coerce_eq
                                                                   pst.Pulse_Checker_Prover_Base.k
                                                                   ()) () ())
                                                             ());
                                                        Pulse_Checker_Prover_Base.goals_inv
                                                          = ();
                                                        Pulse_Checker_Prover_Base.solved_inv
                                                          = ()
                                                      })))) uu___1))) uu___1)