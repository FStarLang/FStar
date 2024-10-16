open Prims
let rec (arith_expr_to_bv :
  FStar_Reflection_V2_Arith.expr ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    match e with
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.MulMod
        (e1, uu___)) ->
        let uu___1 =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_mul"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (31)) (Prims.of_int (8)) (Prims.of_int (31))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (32)) (Prims.of_int (8)) (Prims.of_int (33))
                   (Prims.of_int (27))))) (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvmul"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (32)) (Prims.of_int (8))
                              (Prims.of_int (32)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (33)) (Prims.of_int (8))
                              (Prims.of_int (33)) (Prims.of_int (27)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 -> Obj.magic (arith_expr_to_bv e1))
                          uu___4))) uu___2)
    | FStar_Reflection_V2_Arith.MulMod (e1, uu___) ->
        let uu___1 =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_mul"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (31)) (Prims.of_int (8)) (Prims.of_int (31))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (32)) (Prims.of_int (8)) (Prims.of_int (33))
                   (Prims.of_int (27))))) (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvmul"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (32)) (Prims.of_int (8))
                              (Prims.of_int (32)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (33)) (Prims.of_int (8))
                              (Prims.of_int (33)) (Prims.of_int (27)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 -> Obj.magic (arith_expr_to_bv e1))
                          uu___4))) uu___2)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Umod
        (e1, uu___)) ->
        let uu___1 =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_mod"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (35)) (Prims.of_int (8)) (Prims.of_int (35))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (36)) (Prims.of_int (8)) (Prims.of_int (37))
                   (Prims.of_int (27))))) (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvmod"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (36)) (Prims.of_int (8))
                              (Prims.of_int (36)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (37)) (Prims.of_int (8))
                              (Prims.of_int (37)) (Prims.of_int (27)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 -> Obj.magic (arith_expr_to_bv e1))
                          uu___4))) uu___2)
    | FStar_Reflection_V2_Arith.Umod (e1, uu___) ->
        let uu___1 =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_mod"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (35)) (Prims.of_int (8)) (Prims.of_int (35))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (36)) (Prims.of_int (8)) (Prims.of_int (37))
                   (Prims.of_int (27))))) (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvmod"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (36)) (Prims.of_int (8))
                              (Prims.of_int (36)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (37)) (Prims.of_int (8))
                              (Prims.of_int (37)) (Prims.of_int (27)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 -> Obj.magic (arith_expr_to_bv e1))
                          uu___4))) uu___2)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Udiv
        (e1, uu___)) ->
        let uu___1 =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_div"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (39)) (Prims.of_int (8)) (Prims.of_int (39))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (40)) (Prims.of_int (8)) (Prims.of_int (41))
                   (Prims.of_int (27))))) (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvdiv"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (40)) (Prims.of_int (8))
                              (Prims.of_int (40)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (41)) (Prims.of_int (8))
                              (Prims.of_int (41)) (Prims.of_int (27)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 -> Obj.magic (arith_expr_to_bv e1))
                          uu___4))) uu___2)
    | FStar_Reflection_V2_Arith.Udiv (e1, uu___) ->
        let uu___1 =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_div"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (39)) (Prims.of_int (8)) (Prims.of_int (39))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (40)) (Prims.of_int (8)) (Prims.of_int (41))
                   (Prims.of_int (27))))) (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvdiv"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (40)) (Prims.of_int (8))
                              (Prims.of_int (40)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (41)) (Prims.of_int (8))
                              (Prims.of_int (41)) (Prims.of_int (27)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 -> Obj.magic (arith_expr_to_bv e1))
                          uu___4))) uu___2)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Shl
        (e1, uu___)) ->
        let uu___1 =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_shl"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (43)) (Prims.of_int (8)) (Prims.of_int (43))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (44)) (Prims.of_int (8)) (Prims.of_int (45))
                   (Prims.of_int (27))))) (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvshl"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (44)) (Prims.of_int (8))
                              (Prims.of_int (44)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (45)) (Prims.of_int (8))
                              (Prims.of_int (45)) (Prims.of_int (27)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 -> Obj.magic (arith_expr_to_bv e1))
                          uu___4))) uu___2)
    | FStar_Reflection_V2_Arith.Shl (e1, uu___) ->
        let uu___1 =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_shl"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (43)) (Prims.of_int (8)) (Prims.of_int (43))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (44)) (Prims.of_int (8)) (Prims.of_int (45))
                   (Prims.of_int (27))))) (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvshl"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (44)) (Prims.of_int (8))
                              (Prims.of_int (44)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (45)) (Prims.of_int (8))
                              (Prims.of_int (45)) (Prims.of_int (27)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 -> Obj.magic (arith_expr_to_bv e1))
                          uu___4))) uu___2)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Shr
        (e1, uu___)) ->
        let uu___1 =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_shr"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (47)) (Prims.of_int (8)) (Prims.of_int (47))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (48)) (Prims.of_int (8)) (Prims.of_int (49))
                   (Prims.of_int (27))))) (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvshr"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (48)) (Prims.of_int (8))
                              (Prims.of_int (48)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (49)) (Prims.of_int (8))
                              (Prims.of_int (49)) (Prims.of_int (27)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 -> Obj.magic (arith_expr_to_bv e1))
                          uu___4))) uu___2)
    | FStar_Reflection_V2_Arith.Shr (e1, uu___) ->
        let uu___1 =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_shr"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (47)) (Prims.of_int (8)) (Prims.of_int (47))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (48)) (Prims.of_int (8)) (Prims.of_int (49))
                   (Prims.of_int (27))))) (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvshr"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (48)) (Prims.of_int (8))
                              (Prims.of_int (48)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (49)) (Prims.of_int (8))
                              (Prims.of_int (49)) (Prims.of_int (27)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        (fun uu___4 -> Obj.magic (arith_expr_to_bv e1))
                          uu___4))) uu___2)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Land
        (e1, e2)) ->
        let uu___ =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_logand"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (51)) (Prims.of_int (8)) (Prims.of_int (51))
                   (Prims.of_int (36)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (52)) (Prims.of_int (8)) (Prims.of_int (54))
                   (Prims.of_int (27))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvand"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (52)) (Prims.of_int (8))
                              (Prims.of_int (52)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (53)) (Prims.of_int (8))
                              (Prims.of_int (54)) (Prims.of_int (27)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 = arith_expr_to_bv e1 in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (53))
                                         (Prims.of_int (8))
                                         (Prims.of_int (53))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (54))
                                         (Prims.of_int (8))
                                         (Prims.of_int (54))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun uu___5 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___5)))
                          uu___3))) uu___1)
    | FStar_Reflection_V2_Arith.Land (e1, e2) ->
        let uu___ =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_logand"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (51)) (Prims.of_int (8)) (Prims.of_int (51))
                   (Prims.of_int (36)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (52)) (Prims.of_int (8)) (Prims.of_int (54))
                   (Prims.of_int (27))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvand"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (52)) (Prims.of_int (8))
                              (Prims.of_int (52)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (53)) (Prims.of_int (8))
                              (Prims.of_int (54)) (Prims.of_int (27)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 = arith_expr_to_bv e1 in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (53))
                                         (Prims.of_int (8))
                                         (Prims.of_int (53))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (54))
                                         (Prims.of_int (8))
                                         (Prims.of_int (54))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun uu___5 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___5)))
                          uu___3))) uu___1)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Lxor
        (e1, e2)) ->
        let uu___ =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_logxor"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (56)) (Prims.of_int (8)) (Prims.of_int (56))
                   (Prims.of_int (36)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (57)) (Prims.of_int (8)) (Prims.of_int (59))
                   (Prims.of_int (27))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvxor"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (57)) (Prims.of_int (8))
                              (Prims.of_int (57)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (58)) (Prims.of_int (8))
                              (Prims.of_int (59)) (Prims.of_int (27)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 = arith_expr_to_bv e1 in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (58))
                                         (Prims.of_int (8))
                                         (Prims.of_int (58))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (59))
                                         (Prims.of_int (8))
                                         (Prims.of_int (59))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun uu___5 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___5)))
                          uu___3))) uu___1)
    | FStar_Reflection_V2_Arith.Lxor (e1, e2) ->
        let uu___ =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_logxor"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (56)) (Prims.of_int (8)) (Prims.of_int (56))
                   (Prims.of_int (36)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (57)) (Prims.of_int (8)) (Prims.of_int (59))
                   (Prims.of_int (27))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvxor"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (57)) (Prims.of_int (8))
                              (Prims.of_int (57)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (58)) (Prims.of_int (8))
                              (Prims.of_int (59)) (Prims.of_int (27)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 = arith_expr_to_bv e1 in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (58))
                                         (Prims.of_int (8))
                                         (Prims.of_int (58))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (59))
                                         (Prims.of_int (8))
                                         (Prims.of_int (59))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun uu___5 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___5)))
                          uu___3))) uu___1)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Lor
        (e1, e2)) ->
        let uu___ =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_logor"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (61)) (Prims.of_int (8)) (Prims.of_int (61))
                   (Prims.of_int (35)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (62)) (Prims.of_int (8)) (Prims.of_int (64))
                   (Prims.of_int (27))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvor"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (62)) (Prims.of_int (8))
                              (Prims.of_int (62)) (Prims.of_int (32)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (63)) (Prims.of_int (8))
                              (Prims.of_int (64)) (Prims.of_int (27)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 = arith_expr_to_bv e1 in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (63))
                                         (Prims.of_int (8))
                                         (Prims.of_int (63))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (64))
                                         (Prims.of_int (8))
                                         (Prims.of_int (64))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun uu___5 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___5)))
                          uu___3))) uu___1)
    | FStar_Reflection_V2_Arith.Lor (e1, e2) ->
        let uu___ =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_logor"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (61)) (Prims.of_int (8)) (Prims.of_int (61))
                   (Prims.of_int (35)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (62)) (Prims.of_int (8)) (Prims.of_int (64))
                   (Prims.of_int (27))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvor"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (62)) (Prims.of_int (8))
                              (Prims.of_int (62)) (Prims.of_int (32)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (63)) (Prims.of_int (8))
                              (Prims.of_int (64)) (Prims.of_int (27)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 = arith_expr_to_bv e1 in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (63))
                                         (Prims.of_int (8))
                                         (Prims.of_int (63))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (64))
                                         (Prims.of_int (8))
                                         (Prims.of_int (64))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun uu___5 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___5)))
                          uu___3))) uu___1)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Ladd
        (e1, e2)) ->
        let uu___ =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_add"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (66)) (Prims.of_int (8)) (Prims.of_int (66))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (67)) (Prims.of_int (8)) (Prims.of_int (69))
                   (Prims.of_int (27))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvadd"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (67)) (Prims.of_int (8))
                              (Prims.of_int (67)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (68)) (Prims.of_int (8))
                              (Prims.of_int (69)) (Prims.of_int (27)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 = arith_expr_to_bv e1 in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (68))
                                         (Prims.of_int (8))
                                         (Prims.of_int (68))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (69))
                                         (Prims.of_int (8))
                                         (Prims.of_int (69))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun uu___5 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___5)))
                          uu___3))) uu___1)
    | FStar_Reflection_V2_Arith.Ladd (e1, e2) ->
        let uu___ =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_add"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (66)) (Prims.of_int (8)) (Prims.of_int (66))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (67)) (Prims.of_int (8)) (Prims.of_int (69))
                   (Prims.of_int (27))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvadd"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (67)) (Prims.of_int (8))
                              (Prims.of_int (67)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (68)) (Prims.of_int (8))
                              (Prims.of_int (69)) (Prims.of_int (27)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 = arith_expr_to_bv e1 in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (68))
                                         (Prims.of_int (8))
                                         (Prims.of_int (68))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (69))
                                         (Prims.of_int (8))
                                         (Prims.of_int (69))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun uu___5 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___5)))
                          uu___3))) uu___1)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Lsub
        (e1, e2)) ->
        let uu___ =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_sub"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (71)) (Prims.of_int (8)) (Prims.of_int (71))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (72)) (Prims.of_int (8)) (Prims.of_int (74))
                   (Prims.of_int (27))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvsub"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (72)) (Prims.of_int (8))
                              (Prims.of_int (72)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (73)) (Prims.of_int (8))
                              (Prims.of_int (74)) (Prims.of_int (27)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 = arith_expr_to_bv e1 in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (73))
                                         (Prims.of_int (8))
                                         (Prims.of_int (73))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (74))
                                         (Prims.of_int (8))
                                         (Prims.of_int (74))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun uu___5 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___5)))
                          uu___3))) uu___1)
    | FStar_Reflection_V2_Arith.Lsub (e1, e2) ->
        let uu___ =
          FStar_Tactics_V2_Derived.apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "BV"; "int2bv_sub"]))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (71)) (Prims.of_int (8)) (Prims.of_int (71))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (72)) (Prims.of_int (8)) (Prims.of_int (74))
                   (Prims.of_int (27))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "BV";
                             "Lemmas";
                             "cong_bvsub"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (72)) (Prims.of_int (8))
                              (Prims.of_int (72)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (73)) (Prims.of_int (8))
                              (Prims.of_int (74)) (Prims.of_int (27)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 = arith_expr_to_bv e1 in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (73))
                                         (Prims.of_int (8))
                                         (Prims.of_int (73))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (74))
                                         (Prims.of_int (8))
                                         (Prims.of_int (74))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun uu___5 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___5)))
                          uu___3))) uu___1)
    | uu___ -> FStar_Tactics_V2_Derived.trefl ()
let (arith_to_bv_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.focus
      (fun uu___1 ->
         let uu___2 =
           FStarC_Tactics_V2_Builtins.norm
             [FStar_Pervasives.delta_only ["FStar.BV.bvult"]] in
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (79)) (Prims.of_int (4))
                    (Prims.of_int (79)) (Prims.of_int (40)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (79)) (Prims.of_int (41))
                    (Prims.of_int (93)) (Prims.of_int (65)))))
           (Obj.magic uu___2)
           (fun uu___3 ->
              (fun uu___3 ->
                 let uu___4 = FStar_Tactics_V2_Derived.cur_goal () in
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (80)) (Prims.of_int (12))
                               (Prims.of_int (80)) (Prims.of_int (23)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (80)) (Prims.of_int (26))
                               (Prims.of_int (93)) (Prims.of_int (65)))))
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
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (81))
                                          (Prims.of_int (12))
                                          (Prims.of_int (81))
                                          (Prims.of_int (29)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (82))
                                          (Prims.of_int (4))
                                          (Prims.of_int (93))
                                          (Prims.of_int (65)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    (fun f ->
                                       match f with
                                       | FStar_Reflection_V2_Formula.Comp
                                           (FStar_Reflection_V2_Formula.Eq
                                            uu___6, l, r)
                                           ->
                                           let uu___7 =
                                             FStar_Reflection_V2_Arith.run_tm
                                               (FStar_Reflection_V2_Arith.as_arith_expr
                                                  l) in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (84))
                                                         (Prims.of_int (17))
                                                         (Prims.of_int (84))
                                                         (Prims.of_int (41)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (84))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (90))
                                                         (Prims.of_int (52)))))
                                                (Obj.magic uu___7)
                                                (fun uu___8 ->
                                                   (fun uu___8 ->
                                                      match uu___8 with
                                                      | FStar_Pervasives.Inl
                                                          s ->
                                                          let uu___9 =
                                                            FStarC_Tactics_V2_Builtins.dump
                                                              s in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (16)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (18)))))
                                                               (Obj.magic
                                                                  uu___9)
                                                               (fun uu___10
                                                                  ->
                                                                  (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.trefl
                                                                    ()))
                                                                    uu___10))
                                                      | FStar_Pervasives.Inr
                                                          e ->
                                                          Obj.magic
                                                            (FStar_Tactics_V2_Derived.seq
                                                               (fun uu___9 ->
                                                                  arith_expr_to_bv
                                                                    e)
                                                               FStar_Tactics_V2_Derived.trefl))
                                                     uu___8))
                                       | uu___6 ->
                                           let uu___7 =
                                             let uu___8 =
                                               FStarC_Tactics_V2_Builtins.term_to_string
                                                 g in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.BV.fst"
                                                        (Prims.of_int (93))
                                                        (Prims.of_int (48))
                                                        (Prims.of_int (93))
                                                        (Prims.of_int (64)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Prims.fst"
                                                        (Prims.of_int (611))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (611))
                                                        (Prims.of_int (31)))))
                                               (Obj.magic uu___8)
                                               (fun uu___9 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___10 ->
                                                       Prims.strcat
                                                         "arith_to_bv_tac: unexpected: "
                                                         uu___9)) in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (93))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (93))
                                                         (Prims.of_int (65)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (93))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (93))
                                                         (Prims.of_int (65)))))
                                                (Obj.magic uu___7)
                                                (fun uu___8 ->
                                                   FStar_Tactics_V2_Derived.fail
                                                     uu___8))) uu___6)))
                           uu___5))) uu___3))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.BV.arith_to_bv_tac"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.arith_to_bv_tac (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 arith_to_bv_tac)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (bv_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.focus
      (fun uu___1 ->
         let uu___2 =
           FStar_Tactics_MApply0.mapply0
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "BV"; "Lemmas"; "eq_to_bv"]))) in
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (100)) (Prims.of_int (2))
                    (Prims.of_int (100)) (Prims.of_int (21)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (101)) (Prims.of_int (2))
                    (Prims.of_int (106)) (Prims.of_int (8)))))
           (Obj.magic uu___2)
           (fun uu___3 ->
              (fun uu___3 ->
                 let uu___4 =
                   FStar_Tactics_MApply0.mapply0
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Tactics"; "BV"; "Lemmas"; "trans"]))) in
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (101)) (Prims.of_int (2))
                               (Prims.of_int (101)) (Prims.of_int (18)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (102)) (Prims.of_int (2))
                               (Prims.of_int (106)) (Prims.of_int (8)))))
                      (Obj.magic uu___4)
                      (fun uu___5 ->
                         (fun uu___5 ->
                            let uu___6 = arith_to_bv_tac () in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (102))
                                          (Prims.of_int (2))
                                          (Prims.of_int (102))
                                          (Prims.of_int (20)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (103))
                                          (Prims.of_int (2))
                                          (Prims.of_int (106))
                                          (Prims.of_int (8)))))
                                 (Obj.magic uu___6)
                                 (fun uu___7 ->
                                    (fun uu___7 ->
                                       let uu___8 = arith_to_bv_tac () in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (103))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (103))
                                                     (Prims.of_int (20)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (104))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (106))
                                                     (Prims.of_int (8)))))
                                            (Obj.magic uu___8)
                                            (fun uu___9 ->
                                               (fun uu___9 ->
                                                  let uu___10 =
                                                    FStarC_Tactics_V2_Builtins.set_options
                                                      "--smtencoding.elim_box true" in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.BV.fst"
                                                                (Prims.of_int (104))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (104))
                                                                (Prims.of_int (43)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.BV.fst"
                                                                (Prims.of_int (105))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (106))
                                                                (Prims.of_int (8)))))
                                                       (Obj.magic uu___10)
                                                       (fun uu___11 ->
                                                          (fun uu___11 ->
                                                             let uu___12 =
                                                               FStarC_Tactics_V2_Builtins.norm
                                                                 [FStar_Pervasives.delta] in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (14)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (8)))))
                                                                  (Obj.magic
                                                                    uu___12)
                                                                  (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.smt
                                                                    ()))
                                                                    uu___13)))
                                                            uu___11))) uu___9)))
                                      uu___7))) uu___5))) uu___3))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.BV.bv_tac"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.bv_tac (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 bv_tac)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (bv_tac_lt : Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun n ->
    FStar_Tactics_V2_Derived.focus
      (fun uu___ ->
         let uu___1 =
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___2 ->
                   FStar_Tactics_NamedView.pack
                     (FStar_Tactics_NamedView.Tv_Const
                        (FStarC_Reflection_V2_Data.C_Int n)))) in
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (110)) (Prims.of_int (11))
                    (Prims.of_int (110)) (Prims.of_int (36)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (110)) (Prims.of_int (39))
                    (Prims.of_int (116)) (Prims.of_int (8)))))
           (Obj.magic uu___1)
           (fun uu___2 ->
              (fun nn ->
                 let uu___2 =
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           FStar_Reflection_V2_Derived.mk_app
                             (FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_FVar
                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "BV";
                                      "Lemmas";
                                      "trans_lt2"])))
                             [(nn, FStarC_Reflection_V2_Data.Q_Implicit)])) in
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (111)) (Prims.of_int (10))
                               (Prims.of_int (111)) (Prims.of_int (48)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (112)) (Prims.of_int (2))
                               (Prims.of_int (116)) (Prims.of_int (8)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         (fun t ->
                            let uu___3 =
                              FStar_Tactics_V2_Derived.apply_lemma t in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (112))
                                          (Prims.of_int (2))
                                          (Prims.of_int (112))
                                          (Prims.of_int (15)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (113))
                                          (Prims.of_int (2))
                                          (Prims.of_int (116))
                                          (Prims.of_int (8)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    (fun uu___4 ->
                                       let uu___5 = arith_to_bv_tac () in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (113))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (113))
                                                     (Prims.of_int (20)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (114))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (116))
                                                     (Prims.of_int (8)))))
                                            (Obj.magic uu___5)
                                            (fun uu___6 ->
                                               (fun uu___6 ->
                                                  let uu___7 =
                                                    arith_to_bv_tac () in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.BV.fst"
                                                                (Prims.of_int (114))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (114))
                                                                (Prims.of_int (20)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.BV.fst"
                                                                (Prims.of_int (115))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (116))
                                                                (Prims.of_int (8)))))
                                                       (Obj.magic uu___7)
                                                       (fun uu___8 ->
                                                          (fun uu___8 ->
                                                             let uu___9 =
                                                               FStarC_Tactics_V2_Builtins.set_options
                                                                 "--smtencoding.elim_box true" in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (43)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (8)))))
                                                                  (Obj.magic
                                                                    uu___9)
                                                                  (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.smt
                                                                    ()))
                                                                    uu___10)))
                                                            uu___8))) uu___6)))
                                      uu___4))) uu___3))) uu___2))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.BV.bv_tac_lt"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.bv_tac_lt (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 bv_tac_lt)
               FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_unit
               psc ncb us args)
let (to_bv_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.focus
      (fun uu___1 ->
         let uu___2 =
           FStar_Tactics_V2_Derived.apply_lemma
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "BV"; "Lemmas"; "eq_to_bv"]))) in
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (120)) (Prims.of_int (2))
                    (Prims.of_int (120)) (Prims.of_int (25)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (121)) (Prims.of_int (2))
                    (Prims.of_int (123)) (Prims.of_int (20)))))
           (Obj.magic uu___2)
           (fun uu___3 ->
              (fun uu___3 ->
                 let uu___4 =
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Tactics"; "BV"; "Lemmas"; "trans"]))) in
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (121)) (Prims.of_int (2))
                               (Prims.of_int (121)) (Prims.of_int (22)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (122)) (Prims.of_int (2))
                               (Prims.of_int (123)) (Prims.of_int (20)))))
                      (Obj.magic uu___4)
                      (fun uu___5 ->
                         (fun uu___5 ->
                            let uu___6 = arith_to_bv_tac () in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (122))
                                          (Prims.of_int (2))
                                          (Prims.of_int (122))
                                          (Prims.of_int (20)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (123))
                                          (Prims.of_int (2))
                                          (Prims.of_int (123))
                                          (Prims.of_int (20)))))
                                 (Obj.magic uu___6)
                                 (fun uu___7 ->
                                    (fun uu___7 ->
                                       Obj.magic (arith_to_bv_tac ())) uu___7)))
                           uu___5))) uu___3))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.BV.to_bv_tac"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.to_bv_tac (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 to_bv_tac)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)