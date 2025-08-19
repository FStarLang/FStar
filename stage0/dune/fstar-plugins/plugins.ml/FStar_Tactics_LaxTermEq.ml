open Fstarcompiler
open Prims
type 't comparator_for =
  't -> 't -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr
let opt_eq :
  'a . 'a comparator_for -> 'a FStar_Pervasives_Native.option comparator_for
  =
  fun uu___ ->
    (fun cmp ->
       fun o1 ->
         fun o2 ->
           match (o1, o2) with
           | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> true)))
           | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y)
               -> Obj.magic (Obj.repr (cmp x y))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false))))
      uu___
let either_eq :
  'a 'b .
    'a comparator_for ->
      'b comparator_for ->
        ('a, 'b) Fstarcompiler.FStar_Pervasives.either comparator_for
  =
  fun uu___1 ->
    fun uu___ ->
      (fun cmpa ->
         fun cmpb ->
           fun e1 ->
             fun e2 ->
               match (e1, e2) with
               | (Fstarcompiler.FStar_Pervasives.Inl x,
                  Fstarcompiler.FStar_Pervasives.Inl y) ->
                   Obj.magic (Obj.repr (cmpa x y))
               | (Fstarcompiler.FStar_Pervasives.Inr x,
                  Fstarcompiler.FStar_Pervasives.Inr y) ->
                   Obj.magic (Obj.repr (cmpb x y))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> false)))) uu___1 uu___
let pair_eq :
  'a 'b . 'a comparator_for -> 'b comparator_for -> ('a * 'b) comparator_for
  =
  fun cmpa ->
    fun cmpb ->
      fun uu___ ->
        fun uu___1 ->
          match (uu___, uu___1) with
          | ((a1, b1), (a2, b2)) ->
              let uu___2 = cmpa a1 a2 in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                         (Prims.of_int (26)) (Prims.of_int (5))
                         (Prims.of_int (26)) (Prims.of_int (15)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                         (Prims.of_int (26)) (Prims.of_int (2))
                         (Prims.of_int (26)) (Prims.of_int (42)))))
                (Obj.magic uu___2)
                (fun uu___3 ->
                   (fun uu___3 ->
                      if uu___3
                      then Obj.magic (Obj.repr (cmpb b1 b2))
                      else
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___5 -> false)))) uu___3)
let rec list_eq : 'a . 'a comparator_for -> 'a Prims.list comparator_for =
  fun uu___ ->
    (fun cmp ->
       fun l1 ->
         fun l2 ->
           match (l1, l2) with
           | ([], []) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> true)))
           | (x::xs, y::ys) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = cmp x y in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.LaxTermEq.fst"
                                (Prims.of_int (32)) (Prims.of_int (23))
                                (Prims.of_int (32)) (Prims.of_int (30)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.LaxTermEq.fst"
                                (Prims.of_int (32)) (Prims.of_int (20))
                                (Prims.of_int (32)) (Prims.of_int (64)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             if uu___1
                             then Obj.magic (Obj.repr (list_eq cmp xs ys))
                             else
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 -> false)))) uu___1)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false))))
      uu___
let rec (univ_eq : FStarC_Reflection_Types.universe comparator_for) =
  fun u1 ->
    fun u2 ->
      let uu___ = FStarC_Tactics_V2_Builtins.compress_univ u1 in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (37)) (Prims.of_int (11)) (Prims.of_int (37))
                 (Prims.of_int (27)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (37)) (Prims.of_int (30)) (Prims.of_int (50))
                 (Prims.of_int (14))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun u11 ->
              let uu___1 = FStarC_Tactics_V2_Builtins.compress_univ u2 in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                            (Prims.of_int (38)) (Prims.of_int (11))
                            (Prims.of_int (38)) (Prims.of_int (27)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                            (Prims.of_int (38)) (Prims.of_int (30))
                            (Prims.of_int (50)) (Prims.of_int (14)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun u21 ->
                         let uu___2 =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   FStarC_Reflection_V2_Builtins.inspect_universe
                                     u11)) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.LaxTermEq.fst"
                                       (Prims.of_int (39))
                                       (Prims.of_int (12))
                                       (Prims.of_int (39))
                                       (Prims.of_int (31)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.LaxTermEq.fst"
                                       (Prims.of_int (39))
                                       (Prims.of_int (34))
                                       (Prims.of_int (50))
                                       (Prims.of_int (14)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun uv1 ->
                                    let uu___3 =
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              FStarC_Reflection_V2_Builtins.inspect_universe
                                                u21)) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.LaxTermEq.fst"
                                                  (Prims.of_int (40))
                                                  (Prims.of_int (12))
                                                  (Prims.of_int (40))
                                                  (Prims.of_int (31)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.LaxTermEq.fst"
                                                  (Prims.of_int (41))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (50))
                                                  (Prims.of_int (14)))))
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun uv2 ->
                                               match (uv1, uv2) with
                                               | (FStarC_Reflection_V2_Data.Uv_Zero,
                                                  FStarC_Reflection_V2_Data.Uv_Zero)
                                                   ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              true)))
                                               | (FStarC_Reflection_V2_Data.Uv_Succ
                                                  u12,
                                                  FStarC_Reflection_V2_Data.Uv_Succ
                                                  u22) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (univ_eq u12 u22))
                                               | (FStarC_Reflection_V2_Data.Uv_Max
                                                  us1,
                                                  FStarC_Reflection_V2_Data.Uv_Max
                                                  us2) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (list_eq univ_eq us1
                                                           us2))
                                               | (FStarC_Reflection_V2_Data.Uv_BVar
                                                  v1,
                                                  FStarC_Reflection_V2_Data.Uv_BVar
                                                  v2) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              v1 = v2)))
                                               | (FStarC_Reflection_V2_Data.Uv_Name
                                                  id1,
                                                  FStarC_Reflection_V2_Data.Uv_Name
                                                  id2) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              (FStar_Pervasives_Native.fst
                                                                 (FStarC_Reflection_V2_Builtins.inspect_ident
                                                                    id1))
                                                                =
                                                                (FStar_Pervasives_Native.fst
                                                                   (FStarC_Reflection_V2_Builtins.inspect_ident
                                                                    id2)))))
                                               | (FStarC_Reflection_V2_Data.Uv_Unif
                                                  u12,
                                                  FStarC_Reflection_V2_Data.Uv_Unif
                                                  u22) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              false)))
                                               | (FStarC_Reflection_V2_Data.Uv_Unk,
                                                  FStarC_Reflection_V2_Data.Uv_Unk)
                                                   ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              false)))
                                               | uu___4 ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___5 ->
                                                              false))))
                                              uu___4))) uu___3))) uu___2)))
             uu___1)
let (const_eq : FStarC_Reflection_V2_Data.vconst comparator_for) =
  fun c1 ->
    fun c2 ->
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              match (c1, c2) with
              | (FStarC_Reflection_V2_Data.C_Unit,
                 FStarC_Reflection_V2_Data.C_Unit) -> true
              | (FStarC_Reflection_V2_Data.C_Int i1,
                 FStarC_Reflection_V2_Data.C_Int i2) -> i1 = i2
              | (FStarC_Reflection_V2_Data.C_True,
                 FStarC_Reflection_V2_Data.C_True) -> true
              | (FStarC_Reflection_V2_Data.C_False,
                 FStarC_Reflection_V2_Data.C_False) -> true
              | (FStarC_Reflection_V2_Data.C_String s1,
                 FStarC_Reflection_V2_Data.C_String s2) -> s1 = s2
              | (FStarC_Reflection_V2_Data.C_Range r1,
                 FStarC_Reflection_V2_Data.C_Range r2) -> true
              | (FStarC_Reflection_V2_Data.C_Reify,
                 FStarC_Reflection_V2_Data.C_Reify) -> true
              | (FStarC_Reflection_V2_Data.C_Reflect n1,
                 FStarC_Reflection_V2_Data.C_Reflect n2) -> n1 = n2
              | (FStarC_Reflection_V2_Data.C_Real s1,
                 FStarC_Reflection_V2_Data.C_Real s2) -> s1 = s2
              | uu___1 -> false))
let rec (term_eq : FStarC_Reflection_Types.term comparator_for) =
  fun t1 ->
    fun t2 ->
      let uu___ = FStarC_Tactics_V2_Builtins.compress t1 in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (77)) (Prims.of_int (11)) (Prims.of_int (77))
                 (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (77)) (Prims.of_int (25)) (Prims.of_int (144))
                 (Prims.of_int (14))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun t11 ->
              let uu___1 = FStarC_Tactics_V2_Builtins.compress t2 in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                            (Prims.of_int (78)) (Prims.of_int (11))
                            (Prims.of_int (78)) (Prims.of_int (22)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                            (Prims.of_int (78)) (Prims.of_int (25))
                            (Prims.of_int (144)) (Prims.of_int (14)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun t21 ->
                         let uu___2 =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   FStarC_Reflection_V2_Builtins.inspect_ln
                                     t11)) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.LaxTermEq.fst"
                                       (Prims.of_int (79))
                                       (Prims.of_int (12))
                                       (Prims.of_int (79))
                                       (Prims.of_int (25)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.LaxTermEq.fst"
                                       (Prims.of_int (79))
                                       (Prims.of_int (28))
                                       (Prims.of_int (144))
                                       (Prims.of_int (14)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun tv1 ->
                                    let uu___3 =
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              FStarC_Reflection_V2_Builtins.inspect_ln
                                                t21)) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.LaxTermEq.fst"
                                                  (Prims.of_int (80))
                                                  (Prims.of_int (12))
                                                  (Prims.of_int (80))
                                                  (Prims.of_int (25)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.LaxTermEq.fst"
                                                  (Prims.of_int (81))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (144))
                                                  (Prims.of_int (14)))))
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun tv2 ->
                                               match (tv1, tv2) with
                                               | (FStarC_Reflection_V2_Data.Tv_Unsupp,
                                                  uu___4) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___5 ->
                                                              false)))
                                               | (uu___4,
                                                  FStarC_Reflection_V2_Data.Tv_Unsupp)
                                                   ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___5 ->
                                                              false)))
                                               | (FStarC_Reflection_V2_Data.Tv_Var
                                                  v1,
                                                  FStarC_Reflection_V2_Data.Tv_Var
                                                  v2) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              (FStarC_Reflection_V2_Builtins.inspect_namedv
                                                                 v1).FStarC_Reflection_V2_Data.uniq
                                                                =
                                                                (FStarC_Reflection_V2_Builtins.inspect_namedv
                                                                   v2).FStarC_Reflection_V2_Data.uniq)))
                                               | (FStarC_Reflection_V2_Data.Tv_BVar
                                                  v1,
                                                  FStarC_Reflection_V2_Data.Tv_BVar
                                                  v2) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              (FStarC_Reflection_V2_Builtins.inspect_bv
                                                                 v1).FStarC_Reflection_V2_Data.index
                                                                =
                                                                (FStarC_Reflection_V2_Builtins.inspect_bv
                                                                   v2).FStarC_Reflection_V2_Data.index)))
                                               | (FStarC_Reflection_V2_Data.Tv_FVar
                                                  f1,
                                                  FStarC_Reflection_V2_Data.Tv_FVar
                                                  f2) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                 f1)
                                                                =
                                                                (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                   f2))))
                                               | (FStarC_Reflection_V2_Data.Tv_UInst
                                                  (f1, uu___4),
                                                  FStarC_Reflection_V2_Data.Tv_FVar
                                                  f2) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___5 ->
                                                              (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                 f1)
                                                                =
                                                                (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                   f2))))
                                               | (FStarC_Reflection_V2_Data.Tv_FVar
                                                  f1,
                                                  FStarC_Reflection_V2_Data.Tv_UInst
                                                  (f2, uu___4)) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___5 ->
                                                              (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                 f1)
                                                                =
                                                                (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                   f2))))
                                               | (FStarC_Reflection_V2_Data.Tv_UInst
                                                  (f1, uu___4),
                                                  FStarC_Reflection_V2_Data.Tv_UInst
                                                  (f2, uu___5)) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___6 ->
                                                              (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                 f1)
                                                                =
                                                                (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                   f2))))
                                               | (FStarC_Reflection_V2_Data.Tv_App
                                                  (h1, a1),
                                                  FStarC_Reflection_V2_Data.Tv_App
                                                  (h2, a2)) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (let uu___4 =
                                                           term_eq h1 h2 in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (20)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (49)))))
                                                           (Obj.magic uu___4)
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 if uu___5
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (arg_eq
                                                                    a1 a2))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    false))))
                                                                uu___5)))
                                               | (FStarC_Reflection_V2_Data.Tv_Abs
                                                  (b1, e1),
                                                  FStarC_Reflection_V2_Data.Tv_Abs
                                                  (b2, e2)) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (let uu___4 =
                                                           binder_eq b1 b2 in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (22)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (52)))))
                                                           (Obj.magic uu___4)
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 if uu___5
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (term_eq
                                                                    e1 e2))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    false))))
                                                                uu___5)))
                                               | (FStarC_Reflection_V2_Data.Tv_Arrow
                                                  (b1, c1),
                                                  FStarC_Reflection_V2_Data.Tv_Arrow
                                                  (b2, c2)) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (let uu___4 =
                                                           binder_eq b1 b2 in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (22)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (52)))))
                                                           (Obj.magic uu___4)
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 if uu___5
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (comp_eq
                                                                    c1 c2))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    false))))
                                                                uu___5)))
                                               | (FStarC_Reflection_V2_Data.Tv_Type
                                                  u1,
                                                  FStarC_Reflection_V2_Data.Tv_Type
                                                  u2) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              true)))
                                               | (FStarC_Reflection_V2_Data.Tv_Refine
                                                  (sb1, r1),
                                                  FStarC_Reflection_V2_Data.Tv_Refine
                                                  (sb2, r2)) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (let uu___4 =
                                                           binder_eq sb1 sb2 in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (24)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (54)))))
                                                           (Obj.magic uu___4)
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 if uu___5
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (term_eq
                                                                    r1 r2))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    false))))
                                                                uu___5)))
                                               | (FStarC_Reflection_V2_Data.Tv_Const
                                                  c1,
                                                  FStarC_Reflection_V2_Data.Tv_Const
                                                  c2) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (const_eq c1 c2))
                                               | (FStarC_Reflection_V2_Data.Tv_Uvar
                                                  (n1, _u1),
                                                  FStarC_Reflection_V2_Data.Tv_Uvar
                                                  (n2, _u2)) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              n1 = n2)))
                                               | (FStarC_Reflection_V2_Data.Tv_Let
                                                  (r1, attrs1, sb1, e1, b1),
                                                  FStarC_Reflection_V2_Data.Tv_Let
                                                  (r2, attrs2, sb2, e2, b2))
                                                   ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (if
                                                           (Prims.op_Negation
                                                              r1)
                                                             = r2
                                                         then
                                                           Obj.repr
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   -> false))
                                                         else
                                                           Obj.repr
                                                             (let uu___5 =
                                                                let uu___6 =
                                                                  binder_eq
                                                                    sb1 sb2 in
                                                                FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (31)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (31)))))
                                                                  (Obj.magic
                                                                    uu___6)
                                                                  (fun uu___7
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.op_Negation
                                                                    uu___7)) in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (31)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (17)))))
                                                                (Obj.magic
                                                                   uu___5)
                                                                (fun uu___6
                                                                   ->
                                                                   (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    false)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    term_eq
                                                                    e1 e2 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.op_Negation
                                                                    uu___10)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    if uu___9
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> false)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (term_eq
                                                                    b1 b2)))
                                                                    uu___9))))
                                                                    uu___6))))
                                               | (FStarC_Reflection_V2_Data.Tv_Match
                                                  (sc1, o1, brs1),
                                                  FStarC_Reflection_V2_Data.Tv_Match
                                                  (sc2, o2, brs2)) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (let uu___4 =
                                                           let uu___5 =
                                                             term_eq sc1 sc2 in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (29)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (29)))))
                                                             (Obj.magic
                                                                uu___5)
                                                             (fun uu___6 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___7
                                                                    ->
                                                                    Prims.op_Negation
                                                                    uu___6)) in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (29)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (27)))))
                                                           (Obj.magic uu___4)
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 if uu___5
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    false)))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    opt_eq
                                                                    match_returns_ascription_eq
                                                                    o1 o2 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.op_Negation
                                                                    uu___9)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    if uu___8
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    false)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (list_eq
                                                                    br_eq
                                                                    brs1 brs2)))
                                                                    uu___8))))
                                                                uu___5)))
                                               | (FStarC_Reflection_V2_Data.Tv_AscribedT
                                                  (t12, uu___4, uu___5,
                                                   uu___6),
                                                  uu___7) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (term_eq t12 t21))
                                               | (FStarC_Reflection_V2_Data.Tv_AscribedC
                                                  (t12, uu___4, uu___5,
                                                   uu___6),
                                                  uu___7) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (term_eq t12 t21))
                                               | (uu___4,
                                                  FStarC_Reflection_V2_Data.Tv_AscribedT
                                                  (t22, uu___5, uu___6,
                                                   uu___7)) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (term_eq t11 t22))
                                               | (uu___4,
                                                  FStarC_Reflection_V2_Data.Tv_AscribedC
                                                  (t22, uu___5, uu___6,
                                                   uu___7)) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (term_eq t11 t22))
                                               | (FStarC_Reflection_V2_Data.Tv_Unknown,
                                                  FStarC_Reflection_V2_Data.Tv_Unknown)
                                                   ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              true)))
                                               | uu___4 ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___5 ->
                                                              false))))
                                              uu___4))) uu___3))) uu___2)))
             uu___1)
and (arg_eq : FStarC_Reflection_V2_Data.argv comparator_for) =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((a1, q1), (a2, q2)) ->
          let uu___2 = term_eq a1 a2 in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                     (Prims.of_int (147)) (Prims.of_int (5))
                     (Prims.of_int (147)) (Prims.of_int (18)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                     (Prims.of_int (147)) (Prims.of_int (2))
                     (Prims.of_int (147)) (Prims.of_int (49)))))
            (Obj.magic uu___2)
            (fun uu___3 ->
               (fun uu___3 ->
                  if uu___3
                  then Obj.magic (Obj.repr (aqual_eq q1 q2))
                  else
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> false)))) uu___3)
and (aqual_eq : FStarC_Reflection_V2_Data.aqualv comparator_for) =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | (FStarC_Reflection_V2_Data.Q_Implicit,
         FStarC_Reflection_V2_Data.Q_Implicit) ->
          Obj.magic
            (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> true)))
      | (FStarC_Reflection_V2_Data.Q_Explicit,
         FStarC_Reflection_V2_Data.Q_Explicit) ->
          Obj.magic
            (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> true)))
      | (FStarC_Reflection_V2_Data.Q_Equality,
         FStarC_Reflection_V2_Data.Q_Equality) ->
          Obj.magic
            (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> true)))
      | (FStarC_Reflection_V2_Data.Q_Meta m1,
         FStarC_Reflection_V2_Data.Q_Meta m2) ->
          Obj.magic (Obj.repr (term_eq m1 m2))
      | uu___ ->
          Obj.magic
            (Obj.repr
               (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false)))
and (match_returns_ascription_eq :
  FStarC_Syntax_Syntax.match_returns_ascription comparator_for) =
  fun asc1 ->
    fun asc2 ->
      let uu___ =
        Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> asc1)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (158)) (Prims.of_int (34))
                 (Prims.of_int (158)) (Prims.of_int (38)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (157)) (Prims.of_int (43))
                 (Prims.of_int (163)) (Prims.of_int (11)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (b1, (tc1, tacopt1, eq1)) ->
                  let uu___2 =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> asc2)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.LaxTermEq.fst"
                                (Prims.of_int (159)) (Prims.of_int (34))
                                (Prims.of_int (159)) (Prims.of_int (38)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.LaxTermEq.fst"
                                (Prims.of_int (158)) (Prims.of_int (41))
                                (Prims.of_int (163)) (Prims.of_int (11)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             match uu___3 with
                             | (b2, (tc2, tacopt2, eq2)) ->
                                 let uu___4 =
                                   let uu___5 = binder_eq b1 b2 in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.LaxTermEq.fst"
                                              (Prims.of_int (160))
                                              (Prims.of_int (12))
                                              (Prims.of_int (160))
                                              (Prims.of_int (27)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.LaxTermEq.fst"
                                              (Prims.of_int (160))
                                              (Prims.of_int (5))
                                              (Prims.of_int (160))
                                              (Prims.of_int (27)))))
                                     (Obj.magic uu___5)
                                     (fun uu___6 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___7 ->
                                             Prims.op_Negation uu___6)) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.LaxTermEq.fst"
                                               (Prims.of_int (160))
                                               (Prims.of_int (5))
                                               (Prims.of_int (160))
                                               (Prims.of_int (27)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.LaxTermEq.fst"
                                               (Prims.of_int (160))
                                               (Prims.of_int (2))
                                               (Prims.of_int (163))
                                               (Prims.of_int (11)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         (fun uu___5 ->
                                            if uu___5
                                            then
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___6 -> false)))
                                            else
                                              Obj.magic
                                                (Obj.repr
                                                   (let uu___7 =
                                                      let uu___8 =
                                                        either_eq term_eq
                                                          comp_eq tc1 tc2 in
                                                      FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.LaxTermEq.fst"
                                                                 (Prims.of_int (161))
                                                                 (Prims.of_int (12))
                                                                 (Prims.of_int (161))
                                                                 (Prims.of_int (45)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.LaxTermEq.fst"
                                                                 (Prims.of_int (161))
                                                                 (Prims.of_int (5))
                                                                 (Prims.of_int (161))
                                                                 (Prims.of_int (45)))))
                                                        (Obj.magic uu___8)
                                                        (fun uu___9 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___10 ->
                                                                Prims.op_Negation
                                                                  uu___9)) in
                                                    FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.LaxTermEq.fst"
                                                               (Prims.of_int (161))
                                                               (Prims.of_int (5))
                                                               (Prims.of_int (161))
                                                               (Prims.of_int (45)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.LaxTermEq.fst"
                                                               (Prims.of_int (161))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (163))
                                                               (Prims.of_int (11)))))
                                                      (Obj.magic uu___7)
                                                      (fun uu___8 ->
                                                         (fun uu___8 ->
                                                            if uu___8
                                                            then
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    false)))
                                                            else
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    opt_eq
                                                                    term_eq
                                                                    tacopt1
                                                                    tacopt2 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.op_Negation
                                                                    uu___12)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.LaxTermEq.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    if
                                                                    uu___11
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> false)
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    eq1 = eq2)))))
                                                           uu___8)))) uu___5)))
                            uu___3))) uu___1)
and (binder_eq : FStarC_Reflection_Types.binder comparator_for) =
  fun b1 ->
    fun b2 ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStarC_Reflection_V2_Builtins.inspect_binder b1)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (166)) (Prims.of_int (12))
                 (Prims.of_int (166)) (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (166)) (Prims.of_int (32))
                 (Prims.of_int (170)) (Prims.of_int (37)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun bv1 ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        FStarC_Reflection_V2_Builtins.inspect_binder b2)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                            (Prims.of_int (167)) (Prims.of_int (12))
                            (Prims.of_int (167)) (Prims.of_int (29)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                            (Prims.of_int (168)) (Prims.of_int (2))
                            (Prims.of_int (170)) (Prims.of_int (37)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun bv2 ->
                         let uu___2 =
                           let uu___3 =
                             term_eq bv1.FStarC_Reflection_V2_Data.sort2
                               bv2.FStarC_Reflection_V2_Data.sort2 in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.LaxTermEq.fst"
                                      (Prims.of_int (168))
                                      (Prims.of_int (12))
                                      (Prims.of_int (168))
                                      (Prims.of_int (37)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.LaxTermEq.fst"
                                      (Prims.of_int (168)) (Prims.of_int (5))
                                      (Prims.of_int (168))
                                      (Prims.of_int (37)))))
                             (Obj.magic uu___3)
                             (fun uu___4 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___5 -> Prims.op_Negation uu___4)) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.LaxTermEq.fst"
                                       (Prims.of_int (168))
                                       (Prims.of_int (5))
                                       (Prims.of_int (168))
                                       (Prims.of_int (37)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.LaxTermEq.fst"
                                       (Prims.of_int (168))
                                       (Prims.of_int (2))
                                       (Prims.of_int (170))
                                       (Prims.of_int (37)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun uu___3 ->
                                    if uu___3
                                    then
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___4 -> false)))
                                    else
                                      Obj.magic
                                        (Obj.repr
                                           (let uu___5 =
                                              let uu___6 =
                                                aqual_eq
                                                  bv1.FStarC_Reflection_V2_Data.qual
                                                  bv2.FStarC_Reflection_V2_Data.qual in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.LaxTermEq.fst"
                                                         (Prims.of_int (169))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (169))
                                                         (Prims.of_int (38)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.LaxTermEq.fst"
                                                         (Prims.of_int (169))
                                                         (Prims.of_int (5))
                                                         (Prims.of_int (169))
                                                         (Prims.of_int (38)))))
                                                (Obj.magic uu___6)
                                                (fun uu___7 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___8 ->
                                                        Prims.op_Negation
                                                          uu___7)) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.LaxTermEq.fst"
                                                       (Prims.of_int (169))
                                                       (Prims.of_int (5))
                                                       (Prims.of_int (169))
                                                       (Prims.of_int (38)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.LaxTermEq.fst"
                                                       (Prims.of_int (169))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (170))
                                                       (Prims.of_int (37)))))
                                              (Obj.magic uu___5)
                                              (fun uu___6 ->
                                                 (fun uu___6 ->
                                                    if uu___6
                                                    then
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___7 ->
                                                                 false)))
                                                    else
                                                      Obj.magic
                                                        (Obj.repr
                                                           (list_eq term_eq
                                                              bv1.FStarC_Reflection_V2_Data.attrs
                                                              bv2.FStarC_Reflection_V2_Data.attrs)))
                                                   uu___6)))) uu___3)))
                        uu___2))) uu___1)
and (comp_eq : FStarC_Reflection_Types.comp comparator_for) =
  fun c1 ->
    fun c2 ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStarC_Reflection_V2_Builtins.inspect_comp c1)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (173)) (Prims.of_int (12))
                 (Prims.of_int (173)) (Prims.of_int (27)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (173)) (Prims.of_int (30))
                 (Prims.of_int (195)) (Prims.of_int (14)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun cv1 ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        FStarC_Reflection_V2_Builtins.inspect_comp c2)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                            (Prims.of_int (174)) (Prims.of_int (12))
                            (Prims.of_int (174)) (Prims.of_int (27)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                            (Prims.of_int (175)) (Prims.of_int (2))
                            (Prims.of_int (195)) (Prims.of_int (14)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun cv2 ->
                         match (cv1, cv2) with
                         | (FStarC_Reflection_V2_Data.C_Total t1,
                            FStarC_Reflection_V2_Data.C_Total t2) ->
                             Obj.magic (Obj.repr (term_eq t1 t2))
                         | (FStarC_Reflection_V2_Data.C_GTotal t1,
                            FStarC_Reflection_V2_Data.C_GTotal t2) ->
                             Obj.magic (Obj.repr (term_eq t1 t2))
                         | (FStarC_Reflection_V2_Data.C_Lemma
                            (pre1, post1, pat1),
                            FStarC_Reflection_V2_Data.C_Lemma
                            (pre2, post2, pat2)) ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___2 =
                                     let uu___3 = term_eq pre1 pre2 in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.LaxTermEq.fst"
                                                (Prims.of_int (181))
                                                (Prims.of_int (14))
                                                (Prims.of_int (181))
                                                (Prims.of_int (31)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.LaxTermEq.fst"
                                                (Prims.of_int (181))
                                                (Prims.of_int (7))
                                                (Prims.of_int (181))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___5 ->
                                               Prims.op_Negation uu___4)) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.LaxTermEq.fst"
                                              (Prims.of_int (181))
                                              (Prims.of_int (7))
                                              (Prims.of_int (181))
                                              (Prims.of_int (31)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.LaxTermEq.fst"
                                              (Prims.of_int (181))
                                              (Prims.of_int (4))
                                              (Prims.of_int (183))
                                              (Prims.of_int (21)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        (fun uu___3 ->
                                           if uu___3
                                           then
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 -> false)))
                                           else
                                             Obj.magic
                                               (Obj.repr
                                                  (let uu___5 =
                                                     let uu___6 =
                                                       term_eq post1 post2 in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.LaxTermEq.fst"
                                                                (Prims.of_int (182))
                                                                (Prims.of_int (14))
                                                                (Prims.of_int (182))
                                                                (Prims.of_int (33)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.LaxTermEq.fst"
                                                                (Prims.of_int (182))
                                                                (Prims.of_int (7))
                                                                (Prims.of_int (182))
                                                                (Prims.of_int (33)))))
                                                       (Obj.magic uu___6)
                                                       (fun uu___7 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___8 ->
                                                               Prims.op_Negation
                                                                 uu___7)) in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.LaxTermEq.fst"
                                                              (Prims.of_int (182))
                                                              (Prims.of_int (7))
                                                              (Prims.of_int (182))
                                                              (Prims.of_int (33)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.LaxTermEq.fst"
                                                              (Prims.of_int (182))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (183))
                                                              (Prims.of_int (21)))))
                                                     (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        (fun uu___6 ->
                                                           if uu___6
                                                           then
                                                             Obj.magic
                                                               (Obj.repr
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    false)))
                                                           else
                                                             Obj.magic
                                                               (Obj.repr
                                                                  (term_eq
                                                                    pat1 pat2)))
                                                          uu___6)))) uu___3)))
                         | (FStarC_Reflection_V2_Data.C_Eff
                            (us1, ef1, t1, args1, dec1),
                            FStarC_Reflection_V2_Data.C_Eff
                            (us2, ef2, t2, args2, dec2)) ->
                             Obj.magic
                               (Obj.repr
                                  (if Prims.op_Negation (ef1 = ef2)
                                   then
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 -> false))
                                   else
                                     Obj.repr
                                       (let uu___3 =
                                          let uu___4 = term_eq t1 t2 in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.LaxTermEq.fst"
                                                     (Prims.of_int (189))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (189))
                                                     (Prims.of_int (27)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.LaxTermEq.fst"
                                                     (Prims.of_int (189))
                                                     (Prims.of_int (7))
                                                     (Prims.of_int (189))
                                                     (Prims.of_int (27)))))
                                            (Obj.magic uu___4)
                                            (fun uu___5 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___6 ->
                                                    Prims.op_Negation uu___5)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.LaxTermEq.fst"
                                                   (Prims.of_int (189))
                                                   (Prims.of_int (7))
                                                   (Prims.of_int (189))
                                                   (Prims.of_int (27)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.LaxTermEq.fst"
                                                   (Prims.of_int (189))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (193))
                                                   (Prims.of_int (8)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             if uu___4
                                             then
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___5 -> false)
                                             else
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___6 -> true)))))
                         | uu___2 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> false)))) uu___2)))
             uu___1)
and (br_eq : FStarC_Reflection_V2_Data.branch comparator_for) =
  fun br1 ->
    fun br2 ->
      let uu___ =
        let uu___1 =
          pat_eq (FStar_Pervasives_Native.fst br1)
            (FStar_Pervasives_Native.fst br2) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                   (Prims.of_int (199)) (Prims.of_int (12))
                   (Prims.of_int (199)) (Prims.of_int (38)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                   (Prims.of_int (199)) (Prims.of_int (5))
                   (Prims.of_int (199)) (Prims.of_int (38)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___3 -> Prims.op_Negation uu___2)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (199)) (Prims.of_int (5)) (Prims.of_int (199))
                 (Prims.of_int (38)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (199)) (Prims.of_int (2)) (Prims.of_int (200))
                 (Prims.of_int (29))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              if uu___1
              then
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> false)))
              else
                Obj.magic
                  (Obj.repr
                     (term_eq (FStar_Pervasives_Native.snd br1)
                        (FStar_Pervasives_Native.snd br2)))) uu___1)
and (pat_eq : FStarC_Reflection_V2_Data.pattern comparator_for) =
  fun p1 ->
    fun p2 ->
      match (p1, p2) with
      | (FStarC_Reflection_V2_Data.Pat_Var (v1, sort1),
         FStarC_Reflection_V2_Data.Pat_Var (v2, sort2)) ->
          Obj.magic
            (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> true)))
      | (FStarC_Reflection_V2_Data.Pat_Constant x1,
         FStarC_Reflection_V2_Data.Pat_Constant x2) ->
          Obj.magic (Obj.repr (const_eq x1 x2))
      | (FStarC_Reflection_V2_Data.Pat_Dot_Term x1,
         FStarC_Reflection_V2_Data.Pat_Dot_Term x2) ->
          Obj.magic (Obj.repr (opt_eq term_eq x1 x2))
      | (FStarC_Reflection_V2_Data.Pat_Cons (head1, us1, subpats1),
         FStarC_Reflection_V2_Data.Pat_Cons (head2, us2, subpats2)) ->
          Obj.magic
            (Obj.repr
               (if
                  Prims.op_Negation
                    ((FStarC_Reflection_V2_Builtins.inspect_fv head1) =
                       (FStarC_Reflection_V2_Builtins.inspect_fv head2))
                then
                  Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> false))
                else Obj.repr (list_eq pat_arg_eq subpats1 subpats2)))
      | uu___ ->
          Obj.magic
            (Obj.repr
               (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false)))
and (pat_arg_eq :
  (FStarC_Reflection_V2_Data.pattern * Prims.bool) comparator_for) =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((p1, b1), (p2, b2)) ->
          let uu___2 =
            let uu___3 = pat_eq p1 p2 in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                       (Prims.of_int (217)) (Prims.of_int (12))
                       (Prims.of_int (217)) (Prims.of_int (24)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                       (Prims.of_int (217)) (Prims.of_int (5))
                       (Prims.of_int (217)) (Prims.of_int (24)))))
              (Obj.magic uu___3)
              (fun uu___4 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___5 -> Prims.op_Negation uu___4)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                     (Prims.of_int (217)) (Prims.of_int (5))
                     (Prims.of_int (217)) (Prims.of_int (24)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                     (Prims.of_int (217)) (Prims.of_int (2))
                     (Prims.of_int (218)) (Prims.of_int (9)))))
            (Obj.magic uu___2)
            (fun uu___3 ->
               if uu___3
               then FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> false)
               else FStar_Tactics_Effect.lift_div_tac (fun uu___5 -> b1 = b2))
let (lax_term_eq :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = term_eq t1 t2 in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (221)) (Prims.of_int (10))
                 (Prims.of_int (221)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.LaxTermEq.fst"
                 (Prims.of_int (221)) (Prims.of_int (6)) (Prims.of_int (221))
                 (Prims.of_int (7))))) (Obj.magic uu___)
        (fun r -> FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> r))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.LaxTermEq.lax_term_eq" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.LaxTermEq.lax_term_eq (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 lax_term_eq)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_bool psc ncb us args)
let (lax_univ_eq :
  FStarC_Reflection_Types.universe ->
    FStarC_Reflection_Types.universe ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = fun u1 -> fun u2 -> univ_eq u1 u2
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.LaxTermEq.lax_univ_eq" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.LaxTermEq.lax_univ_eq (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 lax_univ_eq)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe
               Fstarcompiler.FStarC_Syntax_Embeddings.e_bool psc ncb us args)
