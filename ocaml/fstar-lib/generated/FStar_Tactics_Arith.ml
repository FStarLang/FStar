open Prims
let (is_arith_goal :
  unit -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStar_Tactics_V2_Derived.cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
               (Prims.of_int (24)) (Prims.of_int (12)) (Prims.of_int (24))
               (Prims.of_int (23)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
               (Prims.of_int (25)) (Prims.of_int (4)) (Prims.of_int (27))
               (Prims.of_int (16))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun g ->
            let uu___2 =
              FStar_Reflection_V2_Arith.run_tm
                (FStar_Reflection_V2_Arith.is_arith_prop g) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                          (Prims.of_int (25)) (Prims.of_int (10))
                          (Prims.of_int (25)) (Prims.of_int (34)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                          (Prims.of_int (25)) (Prims.of_int (4))
                          (Prims.of_int (27)) (Prims.of_int (16)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___4 ->
                         match uu___3 with
                         | FStar_Pervasives.Inr uu___5 -> true
                         | uu___5 -> false)))) uu___2)
let rec (split_arith : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = is_arith_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
               (Prims.of_int (31)) (Prims.of_int (7)) (Prims.of_int (31))
               (Prims.of_int (23)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
               (Prims.of_int (31)) (Prims.of_int (4)) (Prims.of_int (52))
               (Prims.of_int (7))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            if uu___2
            then
              let uu___3 = FStarC_Tactics_V2_Builtins.prune "" in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                            (Prims.of_int (33)) (Prims.of_int (8))
                            (Prims.of_int (33)) (Prims.of_int (16)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                            (Prims.of_int (34)) (Prims.of_int (8))
                            (Prims.of_int (35)) (Prims.of_int (14)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      (fun uu___4 ->
                         let uu___5 =
                           FStarC_Tactics_V2_Builtins.addns "Prims" in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Arith.fst"
                                       (Prims.of_int (34)) (Prims.of_int (8))
                                       (Prims.of_int (34))
                                       (Prims.of_int (21)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Arith.fst"
                                       (Prims.of_int (35)) (Prims.of_int (8))
                                       (Prims.of_int (35))
                                       (Prims.of_int (14)))))
                              (Obj.magic uu___5)
                              (fun uu___6 ->
                                 (fun uu___6 ->
                                    Obj.magic
                                      (FStar_Tactics_V2_Derived.smt ()))
                                   uu___6))) uu___4))
            else
              (let uu___4 = FStar_Tactics_V2_Derived.cur_goal () in
               Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                             (Prims.of_int (38)) (Prims.of_int (16))
                             (Prims.of_int (38)) (Prims.of_int (27)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "FStar.Tactics.Arith.fst"
                             (Prims.of_int (39)) (Prims.of_int (8))
                             (Prims.of_int (51)) (Prims.of_int (14)))))
                    (Obj.magic uu___4)
                    (fun uu___5 ->
                       (fun g ->
                          let uu___5 =
                            FStar_Reflection_V2_Formula.term_as_formula g in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.Arith.fst"
                                        (Prims.of_int (39))
                                        (Prims.of_int (14))
                                        (Prims.of_int (39))
                                        (Prims.of_int (31)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.Arith.fst"
                                        (Prims.of_int (39))
                                        (Prims.of_int (8))
                                        (Prims.of_int (51))
                                        (Prims.of_int (14)))))
                               (Obj.magic uu___5)
                               (fun uu___6 ->
                                  (fun uu___6 ->
                                     match uu___6 with
                                     | FStar_Reflection_V2_Formula.True_ ->
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_V2_Derived.trivial
                                                 ()))
                                     | FStar_Reflection_V2_Formula.And 
                                         (l, r) ->
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_V2_Derived.seq
                                                 FStar_Tactics_V1_Logic.split
                                                 split_arith))
                                     | FStar_Reflection_V2_Formula.Implies
                                         (p, q) ->
                                         Obj.magic
                                           (Obj.repr
                                              (let uu___7 =
                                                 FStar_Tactics_V2_Logic.implies_intro
                                                   () in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Arith.fst"
                                                          (Prims.of_int (45))
                                                          (Prims.of_int (20))
                                                          (Prims.of_int (45))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Arith.fst"
                                                          (Prims.of_int (46))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (46))
                                                          (Prims.of_int (36)))))
                                                 (Obj.magic uu___7)
                                                 (fun uu___8 ->
                                                    (fun uu___8 ->
                                                       Obj.magic
                                                         (FStar_Tactics_V2_Derived.seq
                                                            split_arith
                                                            FStar_Tactics_V2_Logic.l_revert))
                                                      uu___8)))
                                     | FStar_Reflection_V2_Formula.Forall
                                         (_x, _sort, _p) ->
                                         Obj.magic
                                           (Obj.repr
                                              (let uu___7 =
                                                 FStar_Tactics_V2_Logic.forall_intros
                                                   () in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Arith.fst"
                                                          (Prims.of_int (48))
                                                          (Prims.of_int (21))
                                                          (Prims.of_int (48))
                                                          (Prims.of_int (37)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Arith.fst"
                                                          (Prims.of_int (49))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (49))
                                                          (Prims.of_int (55)))))
                                                 (Obj.magic uu___7)
                                                 (fun uu___8 ->
                                                    (fun bs ->
                                                       Obj.magic
                                                         (FStar_Tactics_V2_Derived.seq
                                                            split_arith
                                                            (fun uu___8 ->
                                                               FStar_Tactics_V2_Logic.l_revert_all
                                                                 bs))) uu___8)))
                                     | uu___7 ->
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___8 -> ())))) uu___6)))
                         uu___5)))) uu___2)