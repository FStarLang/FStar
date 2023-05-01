open Prims
let (is_arith_goal :
  unit -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Arith.fst" (Prims.of_int (24))
         (Prims.of_int (12)) (Prims.of_int (24)) (Prims.of_int (23)))
      (FStar_Range.mk_range "FStar.Tactics.Arith.fst" (Prims.of_int (25))
         (Prims.of_int (4)) (Prims.of_int (27)) (Prims.of_int (16)))
      (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
      (fun uu___1 ->
         (fun g ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                    (Prims.of_int (25)) (Prims.of_int (10))
                    (Prims.of_int (25)) (Prims.of_int (34)))
                 (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                    (Prims.of_int (25)) (Prims.of_int (4))
                    (Prims.of_int (27)) (Prims.of_int (16)))
                 (Obj.magic
                    (FStar_Reflection_Arith.run_tm
                       (FStar_Reflection_Arith.is_arith_prop g)))
                 (fun uu___1 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 ->
                         match uu___1 with
                         | FStar_Pervasives.Inr uu___3 -> true
                         | uu___3 -> false)))) uu___1)
let rec (split_arith : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Arith.fst" (Prims.of_int (31))
         (Prims.of_int (7)) (Prims.of_int (31)) (Prims.of_int (23)))
      (FStar_Range.mk_range "FStar.Tactics.Arith.fst" (Prims.of_int (31))
         (Prims.of_int (4)) (Prims.of_int (52)) (Prims.of_int (7)))
      (Obj.magic (is_arith_goal ()))
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                      (Prims.of_int (33)) (Prims.of_int (8))
                      (Prims.of_int (33)) (Prims.of_int (16)))
                   (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                      (Prims.of_int (34)) (Prims.of_int (8))
                      (Prims.of_int (35)) (Prims.of_int (14)))
                   (Obj.magic (FStar_Tactics_Builtins.prune ""))
                   (fun uu___2 ->
                      (fun uu___2 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                                 (Prims.of_int (34)) (Prims.of_int (8))
                                 (Prims.of_int (34)) (Prims.of_int (21)))
                              (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                                 (Prims.of_int (35)) (Prims.of_int (8))
                                 (Prims.of_int (35)) (Prims.of_int (14)))
                              (Obj.magic
                                 (FStar_Tactics_Builtins.addns "Prims"))
                              (fun uu___3 ->
                                 (fun uu___3 ->
                                    Obj.magic (FStar_Tactics_Derived.smt ()))
                                   uu___3))) uu___2))
            else
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                      (Prims.of_int (38)) (Prims.of_int (16))
                      (Prims.of_int (38)) (Prims.of_int (27)))
                   (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                      (Prims.of_int (39)) (Prims.of_int (8))
                      (Prims.of_int (51)) (Prims.of_int (14)))
                   (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                   (fun uu___3 ->
                      (fun g ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                                 (Prims.of_int (39)) (Prims.of_int (14))
                                 (Prims.of_int (39)) (Prims.of_int (31)))
                              (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                                 (Prims.of_int (39)) (Prims.of_int (8))
                                 (Prims.of_int (51)) (Prims.of_int (14)))
                              (Obj.magic
                                 (FStar_Reflection_Formula.term_as_formula g))
                              (fun uu___3 ->
                                 (fun uu___3 ->
                                    match uu___3 with
                                    | FStar_Reflection_Formula.True_ ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Derived.trivial
                                                ()))
                                    | FStar_Reflection_Formula.And (l, r) ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Derived.seq
                                                FStar_Tactics_Logic.split
                                                split_arith))
                                    | FStar_Reflection_Formula.Implies 
                                        (p, q) ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Arith.fst"
                                                   (Prims.of_int (45))
                                                   (Prims.of_int (20))
                                                   (Prims.of_int (45))
                                                   (Prims.of_int (36)))
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Arith.fst"
                                                   (Prims.of_int (46))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (46))
                                                   (Prims.of_int (36)))
                                                (Obj.magic
                                                   (FStar_Tactics_Logic.implies_intro
                                                      ()))
                                                (fun uu___4 ->
                                                   (fun uu___4 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Derived.seq
                                                           split_arith
                                                           FStar_Tactics_Logic.l_revert))
                                                     uu___4)))
                                    | FStar_Reflection_Formula.Forall
                                        (_x, _sort, _p) ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Arith.fst"
                                                   (Prims.of_int (48))
                                                   (Prims.of_int (21))
                                                   (Prims.of_int (48))
                                                   (Prims.of_int (37)))
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Arith.fst"
                                                   (Prims.of_int (49))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (49))
                                                   (Prims.of_int (55)))
                                                (Obj.magic
                                                   (FStar_Tactics_Logic.forall_intros
                                                      ()))
                                                (fun uu___4 ->
                                                   (fun bs ->
                                                      Obj.magic
                                                        (FStar_Tactics_Derived.seq
                                                           split_arith
                                                           (fun uu___4 ->
                                                              FStar_Tactics_Logic.l_revert_all
                                                                bs))) uu___4)))
                                    | uu___4 ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 -> ())))) uu___3)))
                        uu___3))) uu___1)
