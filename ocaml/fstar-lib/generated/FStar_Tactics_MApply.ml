open Prims
let rec (apply_squash_or_lem :
  Prims.nat ->
    FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    fun t ->
      FStar_Tactics_Derived.try_with
        (fun uu___ -> match () with | () -> FStar_Tactics_Derived.apply t)
        (fun uu___ ->
           FStar_Tactics_Derived.try_with
             (fun uu___1 ->
                match () with
                | () ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "FStar.Tactics.MApply.fst"
                         (Prims.of_int (33)) (Prims.of_int (8))
                         (Prims.of_int (33)) (Prims.of_int (43)))
                      (FStar_Range.mk_range "FStar.Tactics.MApply.fst"
                         (Prims.of_int (33)) (Prims.of_int (45))
                         (Prims.of_int (33)) (Prims.of_int (52)))
                      (Obj.magic
                         (FStar_Tactics_Derived.apply
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar"; "Squash"; "return_squash"])))))
                      (fun uu___2 ->
                         (fun uu___2 ->
                            Obj.magic (FStar_Tactics_Derived.apply t)) uu___2))
             (fun uu___1 ->
                FStar_Tactics_Derived.try_with
                  (fun uu___2 ->
                     match () with
                     | () -> FStar_Tactics_Derived.apply_lemma t)
                  (fun uu___2 ->
                     (fun uu___2 ->
                        if d <= Prims.int_zero
                        then
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Derived.fail
                                  "mapply: out of fuel"))
                        else
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.MApply.fst"
                                     (Prims.of_int (39)) (Prims.of_int (13))
                                     (Prims.of_int (39)) (Prims.of_int (30)))
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.MApply.fst"
                                     (Prims.of_int (39)) (Prims.of_int (33))
                                     (Prims.of_int (88)) (Prims.of_int (41)))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.MApply.fst"
                                           (Prims.of_int (39))
                                           (Prims.of_int (16))
                                           (Prims.of_int (39))
                                           (Prims.of_int (28)))
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.MApply.fst"
                                           (Prims.of_int (39))
                                           (Prims.of_int (13))
                                           (Prims.of_int (39))
                                           (Prims.of_int (30)))
                                        (Obj.magic
                                           (FStar_Tactics_Derived.cur_env ()))
                                        (fun uu___4 ->
                                           (fun uu___4 ->
                                              Obj.magic
                                                (FStar_Tactics_Builtins.tc
                                                   uu___4 t)) uu___4)))
                                  (fun uu___4 ->
                                     (fun ty ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.MApply.fst"
                                                (Prims.of_int (40))
                                                (Prims.of_int (17))
                                                (Prims.of_int (40))
                                                (Prims.of_int (31)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.MApply.fst"
                                                (Prims.of_int (39))
                                                (Prims.of_int (33))
                                                (Prims.of_int (88))
                                                (Prims.of_int (41)))
                                             (Obj.magic
                                                (FStar_Tactics_SyntaxHelpers.collect_arr
                                                   ty))
                                             (fun uu___4 ->
                                                (fun uu___4 ->
                                                   match uu___4 with
                                                   | (tys, c) ->
                                                       (match FStar_Reflection_Builtins.inspect_comp
                                                                c
                                                        with
                                                        | FStar_Reflection_Data.C_Lemma
                                                            (pre, post,
                                                             uu___5)
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (32)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (41)))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    (post,
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Const
                                                                    FStar_Reflection_Data.C_Unit)),
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                                    (
                                                                    fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    post1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (41)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.norm_term
                                                                    [] post1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    post2 ->
                                                                    match 
                                                                    FStar_Reflection_Formula.term_as_formula'
                                                                    post2
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Formula.Implies
                                                                    (p, q) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (38)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "MApply";
                                                                    "push1"])))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___6)))
                                                                    | 
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "mapply: can't apply (1)")))
                                                                    uu___6)))
                                                                    uu___6)))
                                                        | FStar_Reflection_Data.C_Total
                                                            rt ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (match 
                                                                    FStar_Reflection_Derived.unsquash_term
                                                                    rt
                                                                  with
                                                                  | FStar_Pervasives_Native.Some
                                                                    rt1 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (43)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.norm_term
                                                                    [] rt1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun rt2
                                                                    ->
                                                                    match 
                                                                    FStar_Reflection_Formula.term_as_formula'
                                                                    rt2
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Formula.Implies
                                                                    (p, q) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (40)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "MApply";
                                                                    "push1"])))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___5)))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "mapply: can't apply (1)")))
                                                                    uu___5)
                                                                  | FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (20)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.norm_term
                                                                    [] rt))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun rt1
                                                                    ->
                                                                    match 
                                                                    FStar_Reflection_Formula.term_as_formula'
                                                                    rt1
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Formula.Implies
                                                                    (p, q) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (40)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "MApply";
                                                                    "push1"])))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___5))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (20)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Squash";
                                                                    "return_squash"])))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Derived.apply
                                                                    t))
                                                                    uu___6)))
                                                                    uu___5)))
                                                        | uu___5 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Derived.fail
                                                                    "mapply: can't apply (2)"))))
                                                  uu___4))) uu___4)))) uu___2)))
type 'a termable =
  {
  to_term:
    'a -> (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr }
let __proj__Mktermable__item__to_term :
  'a .
    'a termable ->
      'a -> (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr
  = fun projectee -> match projectee with | { to_term;_} -> to_term
let to_term :
  'a .
    'a termable ->
      'a -> (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr
  = fun dict -> __proj__Mktermable__item__to_term dict
let (termable_term : FStar_Reflection_Types.term termable) =
  {
    to_term =
      (fun uu___ ->
         (fun t ->
            Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           uu___)
  }
let (termable_binding : FStar_Reflection_Data.binding termable) =
  { to_term = FStar_Tactics_Derived.binding_to_term }
let (mapply0 :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> apply_squash_or_lem (Prims.of_int (10)) t
let mapply :
  'ty . 'ty termable -> 'ty -> (unit, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    fun x ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.MApply.fst" (Prims.of_int (108))
           (Prims.of_int (10)) (Prims.of_int (108)) (Prims.of_int (19)))
        (FStar_Range.mk_range "FStar.Tactics.MApply.fst" (Prims.of_int (109))
           (Prims.of_int (2)) (Prims.of_int (109)) (Prims.of_int (26)))
        (Obj.magic (to_term uu___ x))
        (fun uu___1 ->
           (fun t -> Obj.magic (apply_squash_or_lem (Prims.of_int (10)) t))
             uu___1)