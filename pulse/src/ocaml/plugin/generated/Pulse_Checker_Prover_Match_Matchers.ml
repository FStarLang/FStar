open Prims

let rec (equational : Pulse_Syntax_Base.term -> Prims.bool) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_App (h, uu___) -> equational h
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
type matching_kind =
  | Syntactic 
  | Strict 
  | Full 
let (uu___is_Syntactic : matching_kind -> Prims.bool) =
  fun projectee -> match projectee with | Syntactic -> true | uu___ -> false
let (uu___is_Strict : matching_kind -> Prims.bool) =
  fun projectee -> match projectee with | Strict -> true | uu___ -> false
let (uu___is_Full : matching_kind -> Prims.bool) =
  fun projectee -> match projectee with | Full -> true | uu___ -> false
let (is_equate_by_smt : FStar_Reflection_Types.term -> Prims.bool) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_FVar fv ->
        let name = FStar_Reflection_V2_Builtins.inspect_fv fv in
        name = ["Pulse"; "Lib"; "Core"; "equate_by_smt"]
    | uu___ -> false
let (is_equate_strict : FStar_Reflection_Types.term -> Prims.bool) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_FVar fv ->
        let name = FStar_Reflection_V2_Builtins.inspect_fv fv in
        name = ["Pulse"; "Lib"; "Core"; "equate_strict"]
    | uu___ -> false
let (is_equate_syntactic : FStar_Reflection_Types.term -> Prims.bool) =
  fun t ->
    match FStar_Reflection_V2_Builtins.inspect_ln t with
    | FStar_Reflection_V2_Data.Tv_FVar fv ->
        let name = FStar_Reflection_V2_Builtins.inspect_fv fv in
        name = ["Pulse"; "Lib"; "Core"; "equate_syntactic"]
    | uu___ -> false
let (matching_kind_from_attr :
  Pulse_Syntax_Base.term Prims.list -> matching_kind) =
  fun ats ->
    if FStar_List_Tot_Base.existsb is_equate_syntactic ats
    then Syntactic
    else
      if FStar_List_Tot_Base.existsb is_equate_strict ats
      then Strict
      else Full
let rec zip3 :
  'a 'b 'c .
    'a Prims.list ->
      'b Prims.list ->
        'c Prims.list ->
          (('a * 'b * 'c) Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun l1 ->
           fun l2 ->
             fun l3 ->
               match (l1, l2, l3) with
               | ([], [], []) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
               | (x::xs, y::ys, z::zs) ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = zip3 xs ys zs in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                    (Prims.of_int (115)) (Prims.of_int (40))
                                    (Prims.of_int (115)) (Prims.of_int (53)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                    (Prims.of_int (115)) (Prims.of_int (27))
                                    (Prims.of_int (115)) (Prims.of_int (53)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> (x, y, z) :: uu___1))))
               | (uu___, uu___1, uu___2) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_V2_Derived.fail
                           "zip3: length mismatch"))) uu___2 uu___1 uu___
let (same_head :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      fun t1 ->
        let uu___ =
          let uu___1 = FStar_Tactics_V2_SyntaxHelpers.hua t0 in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.Match.Matchers.fst"
                     (Prims.of_int (121)) (Prims.of_int (10))
                     (Prims.of_int (121)) (Prims.of_int (18)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.Match.Matchers.fst"
                     (Prims.of_int (121)) (Prims.of_int (10))
                     (Prims.of_int (121)) (Prims.of_int (28)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___3 = FStar_Tactics_V2_SyntaxHelpers.hua t1 in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Matchers.fst"
                                (Prims.of_int (121)) (Prims.of_int (20))
                                (Prims.of_int (121)) (Prims.of_int (28)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Matchers.fst"
                                (Prims.of_int (121)) (Prims.of_int (10))
                                (Prims.of_int (121)) (Prims.of_int (28)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> (uu___2, uu___4))))) uu___2) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "Pulse.Checker.Prover.Match.Matchers.fst"
                   (Prims.of_int (121)) (Prims.of_int (10))
                   (Prims.of_int (121)) (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "Pulse.Checker.Prover.Match.Matchers.fst"
                   (Prims.of_int (121)) (Prims.of_int (4))
                   (Prims.of_int (126)) (Prims.of_int (10)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 ->
                  match uu___1 with
                  | (FStar_Pervasives_Native.Some (h0, us0, args0),
                     FStar_Pervasives_Native.Some (h1, us1, args1)) ->
                      ((FStar_Reflection_V2_Builtins.inspect_fv h0) =
                         (FStar_Reflection_V2_Builtins.inspect_fv h1))
                        &&
                        ((FStar_List_Tot_Base.length args0) =
                           (FStar_List_Tot_Base.length args1))
                  | uu___3 -> true))
let (eligible_for_smt_equality :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      fun t1 ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  fun uu___2 -> (equational t0) || (equational t1))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "Pulse.Checker.Prover.Match.Matchers.fst"
                   (Prims.of_int (130)) (Prims.of_int (31))
                   (Prims.of_int (130)) (Prims.of_int (61)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "Pulse.Checker.Prover.Match.Matchers.fst"
                   (Prims.of_int (130)) (Prims.of_int (64))
                   (Prims.of_int (171)) (Prims.of_int (16)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun either_equational ->
                let uu___1 =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 ->
                          fun t01 ->
                            fun t11 ->
                              FStar_Reflection_TermEq.term_eq t01 t11)) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.Match.Matchers.fst"
                              (Prims.of_int (131)) (Prims.of_int (24))
                              (Prims.of_int (131)) (Prims.of_int (44)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.Match.Matchers.fst"
                              (Prims.of_int (132)) (Prims.of_int (4))
                              (Prims.of_int (171)) (Prims.of_int (16)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun term_eq ->
                           if (term_eq t0 t1) || (either_equational ())
                           then
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> true)))
                           else
                             Obj.magic
                               (Obj.repr
                                  (match ((Pulse_Syntax_Pure.inspect_term t0),
                                           (Pulse_Syntax_Pure.inspect_term t1))
                                   with
                                   | (Pulse_Syntax_Pure.Tm_ForallSL
                                      (uu___3, uu___4, uu___5),
                                      Pulse_Syntax_Pure.Tm_ForallSL
                                      (uu___6, uu___7, uu___8)) ->
                                       Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___9 -> true))
                                   | uu___3 ->
                                       Obj.repr
                                         (let uu___4 =
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___5 ->
                                                    FStar_Reflection_V2_Collect.collect_app_ln
                                                      t0)) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.Match.Matchers.fst"
                                                     (Prims.of_int (137))
                                                     (Prims.of_int (22))
                                                     (Prims.of_int (137))
                                                     (Prims.of_int (41)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.Match.Matchers.fst"
                                                     (Prims.of_int (136))
                                                     (Prims.of_int (11))
                                                     (Prims.of_int (170))
                                                     (Prims.of_int (5)))))
                                            (Obj.magic uu___4)
                                            (fun uu___5 ->
                                               (fun uu___5 ->
                                                  match uu___5 with
                                                  | (h0, args0) ->
                                                      let uu___6 =
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___7 ->
                                                                FStar_Reflection_V2_Collect.collect_app_ln
                                                                  t1)) in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (41)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (16)))))
                                                           (Obj.magic uu___6)
                                                           (fun uu___7 ->
                                                              (fun uu___7 ->
                                                                 match uu___7
                                                                 with
                                                                 | (h1,
                                                                    args1) ->
                                                                    if
                                                                    (term_eq
                                                                    h0 h1) &&
                                                                    ((FStar_List_Tot_Base.length
                                                                    args0) =
                                                                    (FStar_List_Tot_Base.length
                                                                    args1))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    FStar_Reflection_V2_Builtins.inspect_ln
                                                                    h0
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Data.Tv_FVar
                                                                    fv ->
                                                                    Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    type_of_fv
                                                                    g fv in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> false)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    t ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Reflection_V2_Collect.collect_arr_ln_bs
                                                                    t)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (13)))))
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
                                                                    (bs,
                                                                    uu___12)
                                                                    ->
                                                                    if
                                                                    (FStar_List_Tot_Base.length
                                                                    bs) <>
                                                                    (FStar_List_Tot_Base.length
                                                                    args0)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    -> false)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___14
                                                                    =
                                                                    zip3 bs
                                                                    args0
                                                                    args1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    bs_args0_args1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.fold_right
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    fun acc
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    (b,
                                                                    (a0,
                                                                    uu___16),
                                                                    (a1,
                                                                    uu___17))
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    acc
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    -> false)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___19
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (FStar_Reflection_V2_Builtins.inspect_binder
                                                                    b).FStar_Reflection_V2_Data.attrs)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun ats
                                                                    ->
                                                                    match 
                                                                    matching_kind_from_attr
                                                                    ats
                                                                    with
                                                                    | 
                                                                    Syntactic
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    term_eq
                                                                    a0 a1)))
                                                                    | 
                                                                    Strict ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.try_with
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    Pulse_Typing_Util.check_equiv_now_nosmt
                                                                    (Pulse_Typing.elab_env
                                                                    g) a0 a1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___23)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    uu___22)))
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    -> false)))
                                                                    uu___20)))
                                                                    | 
                                                                    Full ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    -> true))))
                                                                    uu___20))))
                                                                    uu___16
                                                                    uu___15)
                                                                    bs_args0_args1
                                                                    true))
                                                                    uu___15))))
                                                                    uu___11))))
                                                                    uu___9))
                                                                    | 
                                                                    FStar_Reflection_V2_Data.Tv_UInst
                                                                    (fv,
                                                                    uu___8)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___9
                                                                    =
                                                                    type_of_fv
                                                                    g fv in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> false)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    t ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Reflection_V2_Collect.collect_arr_ln_bs
                                                                    t)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    uu___13)
                                                                    ->
                                                                    if
                                                                    (FStar_List_Tot_Base.length
                                                                    bs) <>
                                                                    (FStar_List_Tot_Base.length
                                                                    args0)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    -> false)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___15
                                                                    =
                                                                    zip3 bs
                                                                    args0
                                                                    args1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    bs_args0_args1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.fold_right
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    fun acc
                                                                    ->
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    (b,
                                                                    (a0,
                                                                    uu___17),
                                                                    (a1,
                                                                    uu___18))
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    acc
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    -> false)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___20
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (FStar_Reflection_V2_Builtins.inspect_binder
                                                                    b).FStar_Reflection_V2_Data.attrs)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun ats
                                                                    ->
                                                                    match 
                                                                    matching_kind_from_attr
                                                                    ats
                                                                    with
                                                                    | 
                                                                    Syntactic
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    term_eq
                                                                    a0 a1)))
                                                                    | 
                                                                    Strict ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.try_with
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    Pulse_Typing_Util.check_equiv_now_nosmt
                                                                    (Pulse_Typing.elab_env
                                                                    g) a0 a1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___24)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    uu___23)))
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    -> false)))
                                                                    uu___21)))
                                                                    | 
                                                                    Full ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    -> true))))
                                                                    uu___21))))
                                                                    uu___17
                                                                    uu___16)
                                                                    bs_args0_args1
                                                                    true))
                                                                    uu___16))))
                                                                    uu___12))))
                                                                    uu___10))
                                                                    | 
                                                                    uu___8 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    false))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    false))))
                                                                uu___7)))
                                                 uu___5))
                                   | uu___3 ->
                                       Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 -> false))))) uu___2)))
               uu___1)
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
          let uu___ =
            let uu___1 =
              let uu___2 = Pulse_Typing_Env.bindings_with_ppname uvs in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.Match.Matchers.fst"
                         (Prims.of_int (192)) (Prims.of_int (12))
                         (Prims.of_int (193)) (Prims.of_int (27)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.Match.Matchers.fst"
                         (Prims.of_int (192)) (Prims.of_int (12))
                         (Prims.of_int (194)) (Prims.of_int (12)))))
                (Obj.magic uu___2)
                (fun uu___3 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___4 -> FStar_List_Tot_Base.rev uu___3)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "Pulse.Checker.Prover.Match.Matchers.fst"
                       (Prims.of_int (192)) (Prims.of_int (12))
                       (Prims.of_int (194)) (Prims.of_int (12)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "Pulse.Checker.Prover.Match.Matchers.fst"
                       (Prims.of_int (192)) (Prims.of_int (12))
                       (Prims.of_int (203)) (Prims.of_int (8)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___3 ->
                      FStar_List_Tot_Base.map
                        (fun uu___4 ->
                           match uu___4 with
                           | ({ Pulse_Syntax_Base.name = name;
                                Pulse_Syntax_Base.range = uu___5;_},
                              x, t) ->
                               ((FStar_Reflection_V2_Builtins.pack_namedv
                                   (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv
                                      {
                                        FStar_Reflection_V2_Data.uniq1 = x;
                                        FStar_Reflection_V2_Data.sort3 = t;
                                        FStar_Reflection_V2_Data.ppname3 =
                                          name
                                      })), t)) uu___2)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.Match.Matchers.fst"
                     (Prims.of_int (192)) (Prims.of_int (12))
                     (Prims.of_int (203)) (Prims.of_int (8)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.Match.Matchers.fst"
                     (Prims.of_int (203)) (Prims.of_int (11))
                     (Prims.of_int (232)) (Prims.of_int (10)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uvs1 ->
                  let uu___1 =
                    Pulse_RuntimeUtils.with_context
                      (Pulse_Typing_Env.get_context g)
                      (fun uu___2 ->
                         FStar_Tactics_V2_Derived.with_policy
                           FStar_Tactics_Types.ForceSMT
                           (fun uu___3 ->
                              FStar_Tactics_V2_Builtins.try_unify
                                (Pulse_Typing.elab_env g) uvs1 p q)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Matchers.fst"
                                (Prims.of_int (206)) (Prims.of_int (4))
                                (Prims.of_int (208)) (Prims.of_int (42)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Matchers.fst"
                                (Prims.of_int (203)) (Prims.of_int (11))
                                (Prims.of_int (232)) (Prims.of_int (10)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun uu___2 ->
                             match uu___2 with
                             | (l, issues) ->
                                 let uu___3 =
                                   FStar_Tactics_V2_Builtins.log_issues
                                     issues in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.Match.Matchers.fst"
                                               (Prims.of_int (211))
                                               (Prims.of_int (2))
                                               (Prims.of_int (211))
                                               (Prims.of_int (21)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.Match.Matchers.fst"
                                               (Prims.of_int (216))
                                               (Prims.of_int (2))
                                               (Prims.of_int (232))
                                               (Prims.of_int (10)))))
                                      (Obj.magic uu___3)
                                      (fun uu___4 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___5 ->
                                              match l with
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  Pulse_Checker_Prover_Substs.empty
                                              | FStar_Pervasives_Native.Some
                                                  l1 ->
                                                  FStar_List_Tot_Base.fold_left
                                                    (fun ss ->
                                                       fun uu___6 ->
                                                         match uu___6 with
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
                                                    l1)))) uu___2))) uu___1)
let rec (unascribe :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term -> (Pulse_Syntax_Base.term, unit) Prims.dtuple2)
  =
  fun g ->
    fun t ->
      match FStar_Reflection_V2_Builtins.inspect_ln t with
      | FStar_Reflection_V2_Data.Tv_AscribedT (t', uu___, uu___1, uu___2) ->
          let uu___3 = unascribe g t' in
          (match uu___3 with
           | Prims.Mkdtuple2 (t'', tok') -> Prims.Mkdtuple2 (t'', ()))
      | FStar_Reflection_V2_Data.Tv_AscribedC (t', uu___, uu___1, uu___2) ->
          let uu___3 = unascribe g t' in
          (match uu___3 with
           | Prims.Mkdtuple2 (t'', tok') -> Prims.Mkdtuple2 (t'', ()))
      | uu___ -> Prims.Mkdtuple2 (t, ())
let (eq_tm_unascribe :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> unit FStar_Pervasives_Native.option)
  =
  fun g ->
    fun p ->
      fun q ->
        let uu___ = unascribe g p in
        match uu___ with
        | Prims.Mkdtuple2 (up, ptok) ->
            let uu___1 = unascribe g q in
            (match uu___1 with
             | Prims.Mkdtuple2 (uq, qtok) ->
                 if Pulse_Syntax_Base.eq_tm up uq
                 then FStar_Pervasives_Native.Some ()
                 else FStar_Pervasives_Native.None)
let (try_unif_nosmt :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (((unit, unit, unit) FStar_Tactics_Types.equiv_token
           FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      fun q ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_Reflection_V2_Collect.collect_app_ln p)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "Pulse.Checker.Prover.Match.Matchers.fst"
                   (Prims.of_int (264)) (Prims.of_int (19))
                   (Prims.of_int (264)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "Pulse.Checker.Prover.Match.Matchers.fst"
                   (Prims.of_int (263)) (Prims.of_int (100))
                   (Prims.of_int (286)) (Prims.of_int (3)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (hp, args_p) ->
                    let uu___2 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___3 ->
                              FStar_Reflection_V2_Collect.collect_app_ln q)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.Match.Matchers.fst"
                                  (Prims.of_int (265)) (Prims.of_int (19))
                                  (Prims.of_int (265)) (Prims.of_int (37)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Prover.Match.Matchers.fst"
                                  (Prims.of_int (264)) (Prims.of_int (40))
                                  (Prims.of_int (286)) (Prims.of_int (3)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun uu___3 ->
                               match uu___3 with
                               | (hq, args_q) ->
                                   let uu___4 =
                                     if
                                       Pulse_RuntimeUtils.debug_at_level
                                         (Pulse_Typing_Env.fstar_env g) "ggg"
                                     then
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___5 =
                                               let uu___6 =
                                                 Pulse_Typing_Env.range_of_env
                                                   g in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.Match.Matchers.fst"
                                                          (Prims.of_int (267))
                                                          (Prims.of_int (24))
                                                          (Prims.of_int (267))
                                                          (Prims.of_int (38)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.Match.Matchers.fst"
                                                          (Prims.of_int (267))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (267))
                                                          (Prims.of_int (39)))))
                                                 (Obj.magic uu___6)
                                                 (fun uu___7 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___8 ->
                                                         FStar_Pervasives_Native.Some
                                                           uu___7)) in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.Match.Matchers.fst"
                                                        (Prims.of_int (267))
                                                        (Prims.of_int (15))
                                                        (Prims.of_int (267))
                                                        (Prims.of_int (39)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.Match.Matchers.fst"
                                                        (Prims.of_int (267))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (271))
                                                        (Prims.of_int (5)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  (fun uu___6 ->
                                                     let uu___7 =
                                                       let uu___8 =
                                                         let uu___9 =
                                                           let uu___10 =
                                                             Pulse_PP.pp
                                                               Pulse_PP.printable_term
                                                               p in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (24)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (24)))))
                                                             (Obj.magic
                                                                uu___10)
                                                             (fun uu___11 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "p: ")
                                                                    uu___11)) in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (24)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (5)))))
                                                           (Obj.magic uu___9)
                                                           (fun uu___10 ->
                                                              (fun uu___10 ->
                                                                 let uu___11
                                                                   =
                                                                   let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    q in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "q: ")
                                                                    uu___14)) in
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    [uu___13])) in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    uu___10
                                                                    ::
                                                                    uu___12))))
                                                                uu___10) in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                  (Prims.of_int (267))
                                                                  (Prims.of_int (40))
                                                                  (Prims.of_int (271))
                                                                  (Prims.of_int (5)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                  (Prims.of_int (267))
                                                                  (Prims.of_int (40))
                                                                  (Prims.of_int (271))
                                                                  (Prims.of_int (5)))))
                                                         (Obj.magic uu___8)
                                                         (fun uu___9 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___10 ->
                                                                 (Pulse_PP.text
                                                                    "try_unify_nosmt")
                                                                 :: uu___9)) in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                   (Prims.of_int (267))
                                                                   (Prims.of_int (40))
                                                                   (Prims.of_int (271))
                                                                   (Prims.of_int (5)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                   (Prims.of_int (267))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (271))
                                                                   (Prims.of_int (5)))))
                                                          (Obj.magic uu___7)
                                                          (fun uu___8 ->
                                                             (fun uu___8 ->
                                                                Obj.magic
                                                                  (Pulse_Typing_Env.info_doc
                                                                    g uu___6
                                                                    uu___8))
                                                               uu___8)))
                                                    uu___6)))
                                     else
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___6 -> ()))) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Match.Matchers.fst"
                                                 (Prims.of_int (266))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (271))
                                                 (Prims.of_int (5)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Match.Matchers.fst"
                                                 (Prims.of_int (271))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (286))
                                                 (Prims.of_int (3)))))
                                        (Obj.magic uu___4)
                                        (fun uu___5 ->
                                           (fun uu___5 ->
                                              let uu___6 =
                                                if
                                                  FStar_Reflection_TermEq.term_eq
                                                    hp hq
                                                then
                                                  Obj.magic
                                                    (Obj.repr
                                                       (Pulse_Typing_Util.check_equiv_now_nosmt
                                                          (Pulse_Typing.elab_env
                                                             g) p q))
                                                else
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___8 ->
                                                             (FStar_Pervasives_Native.None,
                                                               [])))) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.Match.Matchers.fst"
                                                            (Prims.of_int (274))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (277))
                                                            (Prims.of_int (14)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.Match.Matchers.fst"
                                                            (Prims.of_int (272))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (272))
                                                            (Prims.of_int (7)))))
                                                   (Obj.magic uu___6)
                                                   (fun r ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___7 -> r))))
                                             uu___5))) uu___3))) uu___1)
let (head_is_uvar :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uvs ->
    fun t ->
      let uu___ = FStar_Tactics_V2_SyntaxHelpers.collect_app t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.Match.Matchers.fst"
                 (Prims.of_int (289)) (Prims.of_int (14))
                 (Prims.of_int (289)) (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.Match.Matchers.fst"
                 (Prims.of_int (288)) (Prims.of_int (50))
                 (Prims.of_int (293)) (Prims.of_int (14)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (hd, uu___2) ->
                  let uu___3 = FStar_Tactics_NamedView.inspect hd in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Matchers.fst"
                                (Prims.of_int (290)) (Prims.of_int (8))
                                (Prims.of_int (290)) (Prims.of_int (20)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Matchers.fst"
                                (Prims.of_int (290)) (Prims.of_int (2))
                                (Prims.of_int (293)) (Prims.of_int (14)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 ->
                               match uu___4 with
                               | FStar_Tactics_NamedView.Tv_Var v ->
                                   FStar_List_Tot_Base.existsb
                                     (fun uu___6 ->
                                        match uu___6 with
                                        | (x, uu___7) ->
                                            x =
                                              v.FStar_Reflection_V2_Data.uniq)
                                     (Pulse_Typing_Env.bindings uvs)
                               | uu___6 -> false)))) uu___1)
let (match_syntactic_11 : Pulse_Checker_Prover_Match_Base.matcher_t) =
  fun preamble ->
    fun pst ->
      fun p ->
        fun q ->
          if FStar_Reflection_TermEq.term_eq p q
          then
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Prims.Mkdtuple2 (Pulse_Checker_Prover_Substs.empty, ())))
          else
            Obj.magic
              (FStar_Tactics_Effect.raise
                 (Pulse_Checker_Prover_Match_Base.NoMatch "not term_eq"))
let (match_fastunif_11 : Pulse_Checker_Prover_Match_Base.matcher_t) =
  fun preamble ->
    fun pst ->
      fun p ->
        fun q ->
          let uu___ =
            Pulse_Typing_Util.check_equiv_now_nosmt
              (Pulse_Typing.elab_env pst.Pulse_Checker_Prover_Base.pg) p q in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.Match.Matchers.fst"
                     (Prims.of_int (312)) (Prims.of_int (8))
                     (Prims.of_int (312)) (Prims.of_int (55)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.Match.Matchers.fst"
                     (Prims.of_int (312)) (Prims.of_int (2))
                     (Prims.of_int (314)) (Prims.of_int (40)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               match uu___1 with
               | (FStar_Pervasives_Native.Some tok, uu___2) ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___3 ->
                        Prims.Mkdtuple2
                          (Pulse_Checker_Prover_Substs.empty, ()))
               | (FStar_Pervasives_Native.None, uu___2) ->
                   FStar_Tactics_Effect.raise
                     (Pulse_Checker_Prover_Match_Base.NoMatch "no unif"))
let (match_fastunif_inst_11 : Pulse_Checker_Prover_Match_Base.matcher_t) =
  fun preamble ->
    fun pst ->
      fun p ->
        fun q ->
          let uu___ =
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> pst.Pulse_Checker_Prover_Base.pg)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.Match.Matchers.fst"
                     (Prims.of_int (320)) (Prims.of_int (10))
                     (Prims.of_int (320)) (Prims.of_int (16)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.Match.Matchers.fst"
                     (Prims.of_int (320)) (Prims.of_int (19))
                     (Prims.of_int (363)) (Prims.of_int (21)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun g ->
                  let uu___1 =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> q)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Matchers.fst"
                                (Prims.of_int (321)) (Prims.of_int (11))
                                (Prims.of_int (321)) (Prims.of_int (12)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Matchers.fst"
                                (Prims.of_int (324)) (Prims.of_int (2))
                                (Prims.of_int (363)) (Prims.of_int (21)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun q0 ->
                             let uu___2 =
                               let uu___3 =
                                 let uu___4 =
                                   same_head pst.Pulse_Checker_Prover_Base.pg
                                     p q in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Match.Matchers.fst"
                                            (Prims.of_int (324))
                                            (Prims.of_int (12))
                                            (Prims.of_int (324))
                                            (Prims.of_int (32)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Match.Matchers.fst"
                                            (Prims.of_int (324))
                                            (Prims.of_int (5))
                                            (Prims.of_int (324))
                                            (Prims.of_int (32)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 ->
                                           Prims.op_Negation uu___5)) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.Match.Matchers.fst"
                                          (Prims.of_int (324))
                                          (Prims.of_int (5))
                                          (Prims.of_int (324))
                                          (Prims.of_int (32)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.Match.Matchers.fst"
                                          (Prims.of_int (324))
                                          (Prims.of_int (2))
                                          (Prims.of_int (325))
                                          (Prims.of_int (35)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    if uu___4
                                    then
                                      FStar_Tactics_Effect.raise
                                        (Pulse_Checker_Prover_Match_Base.NoMatch
                                           "head mismatch")
                                    else
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 -> ())) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Prover.Match.Matchers.fst"
                                           (Prims.of_int (324))
                                           (Prims.of_int (2))
                                           (Prims.of_int (325))
                                           (Prims.of_int (35)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Prover.Match.Matchers.fst"
                                           (Prims.of_int (325))
                                           (Prims.of_int (36))
                                           (Prims.of_int (363))
                                           (Prims.of_int (21)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        let uu___4 =
                                          try_solve_uvars
                                            pst.Pulse_Checker_Prover_Base.pg
                                            pst.Pulse_Checker_Prover_Base.uvs
                                            p q in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Prover.Match.Matchers.fst"
                                                      (Prims.of_int (329))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (329))
                                                      (Prims.of_int (46)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Prover.Match.Matchers.fst"
                                                      (Prims.of_int (329))
                                                      (Prims.of_int (49))
                                                      (Prims.of_int (363))
                                                      (Prims.of_int (21)))))
                                             (Obj.magic uu___4)
                                             (fun uu___5 ->
                                                (fun ss' ->
                                                   let uu___5 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___6 ->
                                                             Pulse_Checker_Prover_Base.op_Array_Access
                                                               ss' q)) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                 (Prims.of_int (330))
                                                                 (Prims.of_int (16))
                                                                 (Prims.of_int (330))
                                                                 (Prims.of_int (23)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                 (Prims.of_int (330))
                                                                 (Prims.of_int (26))
                                                                 (Prims.of_int (363))
                                                                 (Prims.of_int (21)))))
                                                        (Obj.magic uu___5)
                                                        (fun uu___6 ->
                                                           (fun q_subst ->
                                                              let uu___6 =
                                                                let uu___7 =
                                                                  FStar_Tactics_V2_Derived.with_policy
                                                                    FStar_Tactics_Types.ForceSMT
                                                                    (
                                                                    fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_V2_Builtins.tc_term
                                                                    (Pulse_Typing.elab_env
                                                                    g)
                                                                    q_subst) in
                                                                FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (77)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (51)))))
                                                                  (Obj.magic
                                                                    uu___7)
                                                                  (fun uu___8
                                                                    ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    (q_subst',
                                                                    uu___9),
                                                                    []) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Builtins.norm_well_typed_term
                                                                    (Pulse_Typing.elab_env
                                                                    g)
                                                                    [FStar_Pervasives.unascribe;
                                                                    FStar_Pervasives.primops;
                                                                    FStar_Pervasives.iota]
                                                                    q_subst'))
                                                                    | 
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.raise
                                                                    (Pulse_Checker_Prover_Match_Base.NoMatch
                                                                    "uvar solution did not check"))))
                                                                    uu___8) in
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (51)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (21)))))
                                                                   (Obj.magic
                                                                    uu___6)
                                                                   (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    q_norm ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    q_subst_eq_q_norm
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g) "ggg"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    Pulse_Typing_Env.range_of_env
                                                                    g in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___11)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    p in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "p: ")
                                                                    uu___15)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    q in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "q: ")
                                                                    uu___18)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    q_subst in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "q_subst: ")
                                                                    uu___21)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    q_norm in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "q_norm: ")
                                                                    uu___24)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    [uu___23])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    uu___20
                                                                    ::
                                                                    uu___22))))
                                                                    uu___20) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    uu___17
                                                                    ::
                                                                    uu___19))))
                                                                    uu___17) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    uu___14
                                                                    ::
                                                                    uu___16))))
                                                                    uu___14) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (Pulse_PP.text
                                                                    "match_fastunif_inst_11")
                                                                    ::
                                                                    uu___13)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.info_doc
                                                                    g uu___10
                                                                    uu___12))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    Pulse_Typing_Util.check_equiv_now_nosmt
                                                                    (Pulse_Typing.elab_env
                                                                    pst.Pulse_Checker_Prover_Base.pg)
                                                                    p q_norm in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    uu___12)
                                                                    ->
                                                                    FStar_Tactics_Effect.raise
                                                                    (Pulse_Checker_Prover_Match_Base.NoMatch
                                                                    "no unif")
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    token,
                                                                    uu___12)
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (ss', ())))))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                             uu___6))) uu___5)))
                                       uu___3))) uu___2))) uu___1)
let (match_full_11 : Pulse_Checker_Prover_Match_Base.matcher_t) =
  fun preamble ->
    fun pst ->
      fun p ->
        fun q ->
          let uu___ =
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> pst.Pulse_Checker_Prover_Base.pg)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.Match.Matchers.fst"
                     (Prims.of_int (371)) (Prims.of_int (10))
                     (Prims.of_int (371)) (Prims.of_int (16)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.Match.Matchers.fst"
                     (Prims.of_int (371)) (Prims.of_int (19))
                     (Prims.of_int (414)) (Prims.of_int (21)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun g ->
                  let uu___1 =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> q)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Matchers.fst"
                                (Prims.of_int (372)) (Prims.of_int (11))
                                (Prims.of_int (372)) (Prims.of_int (12)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Matchers.fst"
                                (Prims.of_int (375)) (Prims.of_int (2))
                                (Prims.of_int (414)) (Prims.of_int (21)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun q0 ->
                             let uu___2 =
                               let uu___3 =
                                 let uu___4 =
                                   same_head pst.Pulse_Checker_Prover_Base.pg
                                     p q in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Match.Matchers.fst"
                                            (Prims.of_int (375))
                                            (Prims.of_int (12))
                                            (Prims.of_int (375))
                                            (Prims.of_int (32)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Match.Matchers.fst"
                                            (Prims.of_int (375))
                                            (Prims.of_int (5))
                                            (Prims.of_int (375))
                                            (Prims.of_int (32)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 ->
                                           Prims.op_Negation uu___5)) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.Match.Matchers.fst"
                                          (Prims.of_int (375))
                                          (Prims.of_int (5))
                                          (Prims.of_int (375))
                                          (Prims.of_int (32)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.Match.Matchers.fst"
                                          (Prims.of_int (375))
                                          (Prims.of_int (2))
                                          (Prims.of_int (376))
                                          (Prims.of_int (35)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    if uu___4
                                    then
                                      FStar_Tactics_Effect.raise
                                        (Pulse_Checker_Prover_Match_Base.NoMatch
                                           "head mismatch")
                                    else
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 -> ())) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Prover.Match.Matchers.fst"
                                           (Prims.of_int (375))
                                           (Prims.of_int (2))
                                           (Prims.of_int (376))
                                           (Prims.of_int (35)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Prover.Match.Matchers.fst"
                                           (Prims.of_int (376))
                                           (Prims.of_int (36))
                                           (Prims.of_int (414))
                                           (Prims.of_int (21)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        let uu___4 =
                                          try_solve_uvars
                                            pst.Pulse_Checker_Prover_Base.pg
                                            pst.Pulse_Checker_Prover_Base.uvs
                                            p q in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Prover.Match.Matchers.fst"
                                                      (Prims.of_int (380))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (380))
                                                      (Prims.of_int (46)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Prover.Match.Matchers.fst"
                                                      (Prims.of_int (380))
                                                      (Prims.of_int (49))
                                                      (Prims.of_int (414))
                                                      (Prims.of_int (21)))))
                                             (Obj.magic uu___4)
                                             (fun uu___5 ->
                                                (fun ss' ->
                                                   let uu___5 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___6 ->
                                                             Pulse_Checker_Prover_Base.op_Array_Access
                                                               ss' q)) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                 (Prims.of_int (381))
                                                                 (Prims.of_int (16))
                                                                 (Prims.of_int (381))
                                                                 (Prims.of_int (23)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                 (Prims.of_int (381))
                                                                 (Prims.of_int (26))
                                                                 (Prims.of_int (414))
                                                                 (Prims.of_int (21)))))
                                                        (Obj.magic uu___5)
                                                        (fun uu___6 ->
                                                           (fun q_subst ->
                                                              let uu___6 =
                                                                let uu___7 =
                                                                  FStar_Tactics_V2_Derived.with_policy
                                                                    FStar_Tactics_Types.ForceSMT
                                                                    (
                                                                    fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_V2_Builtins.tc_term
                                                                    (Pulse_Typing.elab_env
                                                                    g)
                                                                    q_subst) in
                                                                FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (77)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (51)))))
                                                                  (Obj.magic
                                                                    uu___7)
                                                                  (fun uu___8
                                                                    ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    (q_subst',
                                                                    uu___9),
                                                                    []) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Builtins.norm_well_typed_term
                                                                    (Pulse_Typing.elab_env
                                                                    g)
                                                                    [FStar_Pervasives.unascribe;
                                                                    FStar_Pervasives.primops;
                                                                    FStar_Pervasives.iota]
                                                                    q_subst'))
                                                                    | 
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.raise
                                                                    (Pulse_Checker_Prover_Match_Base.NoMatch
                                                                    "uvar solution did not check"))))
                                                                    uu___8) in
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (51)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (21)))))
                                                                   (Obj.magic
                                                                    uu___6)
                                                                   (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    q_norm ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    q_subst_eq_q_norm
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    eligible_for_smt_equality
                                                                    g p
                                                                    q_norm in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Prims.op_Negation
                                                                    uu___11)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    if
                                                                    uu___10
                                                                    then
                                                                    FStar_Tactics_Effect.raise
                                                                    (Pulse_Checker_Prover_Match_Base.NoMatch
                                                                    "not eligible for SMT")
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    Pulse_Typing_Util.check_equiv_now
                                                                    (Pulse_Typing.elab_env
                                                                    g) p
                                                                    q_norm in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Matchers.fst"
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    uu___12)
                                                                    ->
                                                                    FStar_Tactics_Effect.raise
                                                                    (Pulse_Checker_Prover_Match_Base.NoMatch
                                                                    "no unif")
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    token,
                                                                    uu___12)
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (ss', ())))))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                             uu___6))) uu___5)))
                                       uu___3))) uu___2))) uu___1)