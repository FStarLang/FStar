open Prims
let rec (arith_expr_to_bv :
  FStar_Reflection_V2_Arith.expr ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    match e with
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.MulMod
        (e1, uu___)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (30)) (Prims.of_int (8)) (Prims.of_int (30))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (31)) (Prims.of_int (8)) (Prims.of_int (32))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_mul"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (31)) (Prims.of_int (8))
                              (Prims.of_int (31)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (32)) (Prims.of_int (8))
                              (Prims.of_int (32)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvmul"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_V2_Arith.MulMod (e1, uu___) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (30)) (Prims.of_int (8)) (Prims.of_int (30))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (31)) (Prims.of_int (8)) (Prims.of_int (32))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_mul"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (31)) (Prims.of_int (8))
                              (Prims.of_int (31)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (32)) (Prims.of_int (8))
                              (Prims.of_int (32)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvmul"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Umod
        (e1, uu___)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (34)) (Prims.of_int (8)) (Prims.of_int (34))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (35)) (Prims.of_int (8)) (Prims.of_int (36))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_mod"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (35)) (Prims.of_int (8))
                              (Prims.of_int (35)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (36)) (Prims.of_int (8))
                              (Prims.of_int (36)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvmod"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_V2_Arith.Umod (e1, uu___) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (34)) (Prims.of_int (8)) (Prims.of_int (34))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (35)) (Prims.of_int (8)) (Prims.of_int (36))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_mod"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (35)) (Prims.of_int (8))
                              (Prims.of_int (35)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (36)) (Prims.of_int (8))
                              (Prims.of_int (36)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvmod"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Udiv
        (e1, uu___)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (38)) (Prims.of_int (8)) (Prims.of_int (38))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (39)) (Prims.of_int (8)) (Prims.of_int (40))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_div"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (39)) (Prims.of_int (8))
                              (Prims.of_int (39)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (40)) (Prims.of_int (8))
                              (Prims.of_int (40)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvdiv"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_V2_Arith.Udiv (e1, uu___) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (38)) (Prims.of_int (8)) (Prims.of_int (38))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (39)) (Prims.of_int (8)) (Prims.of_int (40))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_div"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (39)) (Prims.of_int (8))
                              (Prims.of_int (39)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (40)) (Prims.of_int (8))
                              (Prims.of_int (40)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvdiv"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Shl
        (e1, uu___)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (42)) (Prims.of_int (8)) (Prims.of_int (42))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (43)) (Prims.of_int (8)) (Prims.of_int (44))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_shl"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (43)) (Prims.of_int (8))
                              (Prims.of_int (43)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (44)) (Prims.of_int (8))
                              (Prims.of_int (44)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvshl"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_V2_Arith.Shl (e1, uu___) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (42)) (Prims.of_int (8)) (Prims.of_int (42))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (43)) (Prims.of_int (8)) (Prims.of_int (44))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_shl"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (43)) (Prims.of_int (8))
                              (Prims.of_int (43)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (44)) (Prims.of_int (8))
                              (Prims.of_int (44)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvshl"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Shr
        (e1, uu___)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (46)) (Prims.of_int (8)) (Prims.of_int (46))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (47)) (Prims.of_int (8)) (Prims.of_int (48))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_shr"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (47)) (Prims.of_int (8))
                              (Prims.of_int (47)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (48)) (Prims.of_int (8))
                              (Prims.of_int (48)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvshr"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_V2_Arith.Shr (e1, uu___) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (46)) (Prims.of_int (8)) (Prims.of_int (46))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (47)) (Prims.of_int (8)) (Prims.of_int (48))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_shr"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (47)) (Prims.of_int (8))
                              (Prims.of_int (47)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (48)) (Prims.of_int (8))
                              (Prims.of_int (48)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvshr"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Land
        (e1, e2)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (50)) (Prims.of_int (8)) (Prims.of_int (50))
                   (Prims.of_int (36)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (51)) (Prims.of_int (8)) (Prims.of_int (53))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logand"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (51)) (Prims.of_int (8))
                              (Prims.of_int (51)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (52)) (Prims.of_int (8))
                              (Prims.of_int (53)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvand"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (52))
                                         (Prims.of_int (8))
                                         (Prims.of_int (52))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (53))
                                         (Prims.of_int (8))
                                         (Prims.of_int (53))
                                         (Prims.of_int (27)))))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_V2_Arith.Land (e1, e2) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (50)) (Prims.of_int (8)) (Prims.of_int (50))
                   (Prims.of_int (36)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (51)) (Prims.of_int (8)) (Prims.of_int (53))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logand"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (51)) (Prims.of_int (8))
                              (Prims.of_int (51)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (52)) (Prims.of_int (8))
                              (Prims.of_int (53)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvand"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (52))
                                         (Prims.of_int (8))
                                         (Prims.of_int (52))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (53))
                                         (Prims.of_int (8))
                                         (Prims.of_int (53))
                                         (Prims.of_int (27)))))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Lxor
        (e1, e2)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (55)) (Prims.of_int (8)) (Prims.of_int (55))
                   (Prims.of_int (36)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (56)) (Prims.of_int (8)) (Prims.of_int (58))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logxor"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (56)) (Prims.of_int (8))
                              (Prims.of_int (56)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (57)) (Prims.of_int (8))
                              (Prims.of_int (58)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvxor"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (57))
                                         (Prims.of_int (8))
                                         (Prims.of_int (57))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (58))
                                         (Prims.of_int (8))
                                         (Prims.of_int (58))
                                         (Prims.of_int (27)))))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_V2_Arith.Lxor (e1, e2) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (55)) (Prims.of_int (8)) (Prims.of_int (55))
                   (Prims.of_int (36)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (56)) (Prims.of_int (8)) (Prims.of_int (58))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logxor"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (56)) (Prims.of_int (8))
                              (Prims.of_int (56)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (57)) (Prims.of_int (8))
                              (Prims.of_int (58)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvxor"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (57))
                                         (Prims.of_int (8))
                                         (Prims.of_int (57))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (58))
                                         (Prims.of_int (8))
                                         (Prims.of_int (58))
                                         (Prims.of_int (27)))))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Lor
        (e1, e2)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (60)) (Prims.of_int (8)) (Prims.of_int (60))
                   (Prims.of_int (35)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (61)) (Prims.of_int (8)) (Prims.of_int (63))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logor"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (61)) (Prims.of_int (8))
                              (Prims.of_int (61)) (Prims.of_int (32)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (62)) (Prims.of_int (8))
                              (Prims.of_int (63)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvor"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (62))
                                         (Prims.of_int (8))
                                         (Prims.of_int (62))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (63))
                                         (Prims.of_int (8))
                                         (Prims.of_int (63))
                                         (Prims.of_int (27)))))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_V2_Arith.Lor (e1, e2) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (60)) (Prims.of_int (8)) (Prims.of_int (60))
                   (Prims.of_int (35)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (61)) (Prims.of_int (8)) (Prims.of_int (63))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logor"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (61)) (Prims.of_int (8))
                              (Prims.of_int (61)) (Prims.of_int (32)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (62)) (Prims.of_int (8))
                              (Prims.of_int (63)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvor"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (62))
                                         (Prims.of_int (8))
                                         (Prims.of_int (62))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (63))
                                         (Prims.of_int (8))
                                         (Prims.of_int (63))
                                         (Prims.of_int (27)))))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Ladd
        (e1, e2)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (65)) (Prims.of_int (8)) (Prims.of_int (65))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (66)) (Prims.of_int (8)) (Prims.of_int (68))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_add"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (66)) (Prims.of_int (8))
                              (Prims.of_int (66)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (67)) (Prims.of_int (8))
                              (Prims.of_int (68)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvadd"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (67))
                                         (Prims.of_int (8))
                                         (Prims.of_int (67))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (68))
                                         (Prims.of_int (8))
                                         (Prims.of_int (68))
                                         (Prims.of_int (27)))))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_V2_Arith.Ladd (e1, e2) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (65)) (Prims.of_int (8)) (Prims.of_int (65))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (66)) (Prims.of_int (8)) (Prims.of_int (68))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_add"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (66)) (Prims.of_int (8))
                              (Prims.of_int (66)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (67)) (Prims.of_int (8))
                              (Prims.of_int (68)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvadd"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (67))
                                         (Prims.of_int (8))
                                         (Prims.of_int (67))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (68))
                                         (Prims.of_int (8))
                                         (Prims.of_int (68))
                                         (Prims.of_int (27)))))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Lsub
        (e1, e2)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (70)) (Prims.of_int (8)) (Prims.of_int (70))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (71)) (Prims.of_int (8)) (Prims.of_int (73))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_sub"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (71)) (Prims.of_int (8))
                              (Prims.of_int (71)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (72)) (Prims.of_int (8))
                              (Prims.of_int (73)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvsub"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (72))
                                         (Prims.of_int (8))
                                         (Prims.of_int (72))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (73))
                                         (Prims.of_int (8))
                                         (Prims.of_int (73))
                                         (Prims.of_int (27)))))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_V2_Arith.Lsub (e1, e2) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (70)) (Prims.of_int (8)) (Prims.of_int (70))
                   (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                   (Prims.of_int (71)) (Prims.of_int (8)) (Prims.of_int (73))
                   (Prims.of_int (27)))))
          (Obj.magic
             (FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_sub"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (71)) (Prims.of_int (8))
                              (Prims.of_int (71)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                              (Prims.of_int (72)) (Prims.of_int (8))
                              (Prims.of_int (73)) (Prims.of_int (27)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "BV";
                                    "Lemmas";
                                    "cong_bvsub"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (72))
                                         (Prims.of_int (8))
                                         (Prims.of_int (72))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.BV.fst"
                                         (Prims.of_int (73))
                                         (Prims.of_int (8))
                                         (Prims.of_int (73))
                                         (Prims.of_int (27)))))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | uu___ -> FStar_Tactics_V2_Derived.trefl ()
let (arith_to_bv_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.focus
      (fun uu___1 ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (78)) (Prims.of_int (4))
                    (Prims.of_int (78)) (Prims.of_int (40)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (78)) (Prims.of_int (41))
                    (Prims.of_int (92)) (Prims.of_int (65)))))
           (Obj.magic
              (FStar_Tactics_V2_Builtins.norm
                 [FStar_Pervasives.delta_only ["FStar.BV.bvult"]]))
           (fun uu___2 ->
              (fun uu___2 ->
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (79)) (Prims.of_int (12))
                               (Prims.of_int (79)) (Prims.of_int (23)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (79)) (Prims.of_int (26))
                               (Prims.of_int (92)) (Prims.of_int (65)))))
                      (Obj.magic (FStar_Tactics_V2_Derived.cur_goal ()))
                      (fun uu___3 ->
                         (fun g ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (80))
                                          (Prims.of_int (12))
                                          (Prims.of_int (80))
                                          (Prims.of_int (29)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (81))
                                          (Prims.of_int (4))
                                          (Prims.of_int (92))
                                          (Prims.of_int (65)))))
                                 (Obj.magic
                                    (FStar_Reflection_V2_Formula.term_as_formula
                                       g))
                                 (fun uu___3 ->
                                    (fun f ->
                                       match f with
                                       | FStar_Reflection_V2_Formula.Comp
                                           (FStar_Reflection_V2_Formula.Eq
                                            uu___3, l, r)
                                           ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (83))
                                                         (Prims.of_int (17))
                                                         (Prims.of_int (83))
                                                         (Prims.of_int (41)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (83))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (89))
                                                         (Prims.of_int (52)))))
                                                (Obj.magic
                                                   (FStar_Reflection_V2_Arith.run_tm
                                                      (FStar_Reflection_V2_Arith.as_arith_expr
                                                         l)))
                                                (fun uu___4 ->
                                                   (fun uu___4 ->
                                                      match uu___4 with
                                                      | FStar_Pervasives.Inl
                                                          s ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (16)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (18)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_V2_Builtins.dump
                                                                    s))
                                                               (fun uu___5 ->
                                                                  (fun uu___5
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.trefl
                                                                    ()))
                                                                    uu___5))
                                                      | FStar_Pervasives.Inr
                                                          e ->
                                                          Obj.magic
                                                            (FStar_Tactics_V2_Derived.seq
                                                               (fun uu___5 ->
                                                                  arith_expr_to_bv
                                                                    e)
                                                               FStar_Tactics_V2_Derived.trefl))
                                                     uu___4))
                                       | uu___3 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (92))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (92))
                                                         (Prims.of_int (65)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (92))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (92))
                                                         (Prims.of_int (65)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.BV.fst"
                                                               (Prims.of_int (92))
                                                               (Prims.of_int (48))
                                                               (Prims.of_int (92))
                                                               (Prims.of_int (64)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "prims.fst"
                                                               (Prims.of_int (595))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (595))
                                                               (Prims.of_int (31)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_V2_Builtins.term_to_string
                                                            g))
                                                      (fun uu___4 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___5 ->
                                                              Prims.strcat
                                                                "arith_to_bv_tac: unexpected: "
                                                                uu___4))))
                                                (fun uu___4 ->
                                                   FStar_Tactics_V2_Derived.fail
                                                     uu___4))) uu___3)))
                           uu___3))) uu___2))
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.BV.arith_to_bv_tac"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.arith_to_bv_tac (plugin)"
               (FStar_Tactics_Native.from_tactic_1 arith_to_bv_tac)
               FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
               psc ncb us args)
let (bv_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.focus
      (fun uu___1 ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (99)) (Prims.of_int (2))
                    (Prims.of_int (99)) (Prims.of_int (20)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (100)) (Prims.of_int (2))
                    (Prims.of_int (105)) (Prims.of_int (8)))))
           (Obj.magic
              (FStar_Tactics_MApply.mapply FStar_Tactics_MApply.termable_term
                 (FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_FVar
                       (FStar_Reflection_V2_Builtins.pack_fv
                          ["FStar"; "Tactics"; "BV"; "Lemmas"; "eq_to_bv"])))))
           (fun uu___2 ->
              (fun uu___2 ->
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (100)) (Prims.of_int (2))
                               (Prims.of_int (100)) (Prims.of_int (17)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (101)) (Prims.of_int (2))
                               (Prims.of_int (105)) (Prims.of_int (8)))))
                      (Obj.magic
                         (FStar_Tactics_MApply.mapply
                            FStar_Tactics_MApply.termable_term
                            (FStar_Reflection_V2_Builtins.pack_ln
                               (FStar_Reflection_V2_Data.Tv_FVar
                                  (FStar_Reflection_V2_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "BV";
                                     "Lemmas";
                                     "trans"])))))
                      (fun uu___3 ->
                         (fun uu___3 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (101))
                                          (Prims.of_int (2))
                                          (Prims.of_int (101))
                                          (Prims.of_int (20)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (102))
                                          (Prims.of_int (2))
                                          (Prims.of_int (105))
                                          (Prims.of_int (8)))))
                                 (Obj.magic (arith_to_bv_tac ()))
                                 (fun uu___4 ->
                                    (fun uu___4 ->
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
                                                     (Prims.of_int (105))
                                                     (Prims.of_int (8)))))
                                            (Obj.magic (arith_to_bv_tac ()))
                                            (fun uu___5 ->
                                               (fun uu___5 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.BV.fst"
                                                                (Prims.of_int (103))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (103))
                                                                (Prims.of_int (43)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.BV.fst"
                                                                (Prims.of_int (104))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (105))
                                                                (Prims.of_int (8)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_V2_Builtins.set_options
                                                             "--smtencoding.elim_box true"))
                                                       (fun uu___6 ->
                                                          (fun uu___6 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (14)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (8)))))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.norm
                                                                    [FStar_Pervasives.delta]))
                                                                  (fun uu___7
                                                                    ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.smt
                                                                    ()))
                                                                    uu___7)))
                                                            uu___6))) uu___5)))
                                      uu___4))) uu___3))) uu___2))
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.BV.bv_tac"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.bv_tac (plugin)"
               (FStar_Tactics_Native.from_tactic_1 bv_tac)
               FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
               psc ncb us args)
let (bv_tac_lt : Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun n ->
    FStar_Tactics_V2_Derived.focus
      (fun uu___ ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (109)) (Prims.of_int (11))
                    (Prims.of_int (109)) (Prims.of_int (36)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (109)) (Prims.of_int (39))
                    (Prims.of_int (115)) (Prims.of_int (8)))))
           (FStar_Tactics_Effect.lift_div_tac
              (fun uu___1 ->
                 FStar_Tactics_NamedView.pack
                   (FStar_Tactics_NamedView.Tv_Const
                      (FStar_Reflection_V2_Data.C_Int n))))
           (fun uu___1 ->
              (fun nn ->
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (110)) (Prims.of_int (10))
                               (Prims.of_int (110)) (Prims.of_int (48)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (111)) (Prims.of_int (2))
                               (Prims.of_int (115)) (Prims.of_int (8)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            FStar_Reflection_V2_Derived.mk_app
                              (FStar_Reflection_V2_Builtins.pack_ln
                                 (FStar_Reflection_V2_Data.Tv_FVar
                                    (FStar_Reflection_V2_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "Lemmas";
                                       "trans_lt2"])))
                              [(nn, FStar_Reflection_V2_Data.Q_Implicit)]))
                      (fun uu___1 ->
                         (fun t ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (111))
                                          (Prims.of_int (2))
                                          (Prims.of_int (111))
                                          (Prims.of_int (15)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (112))
                                          (Prims.of_int (2))
                                          (Prims.of_int (115))
                                          (Prims.of_int (8)))))
                                 (Obj.magic
                                    (FStar_Tactics_V2_Derived.apply_lemma t))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (112))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (112))
                                                     (Prims.of_int (20)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (113))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (115))
                                                     (Prims.of_int (8)))))
                                            (Obj.magic (arith_to_bv_tac ()))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
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
                                                                (Prims.of_int (115))
                                                                (Prims.of_int (8)))))
                                                       (Obj.magic
                                                          (arith_to_bv_tac ()))
                                                       (fun uu___3 ->
                                                          (fun uu___3 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (43)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (8)))))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.set_options
                                                                    "--smtencoding.elim_box true"))
                                                                  (fun uu___4
                                                                    ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.smt
                                                                    ()))
                                                                    uu___4)))
                                                            uu___3))) uu___2)))
                                      uu___1))) uu___1))) uu___1))
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.BV.bv_tac_lt"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.bv_tac_lt (plugin)"
               (FStar_Tactics_Native.from_tactic_1 bv_tac_lt)
               FStar_Syntax_Embeddings.e_int FStar_Syntax_Embeddings.e_unit
               psc ncb us args)
let (to_bv_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.focus
      (fun uu___1 ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (119)) (Prims.of_int (2))
                    (Prims.of_int (119)) (Prims.of_int (25)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                    (Prims.of_int (120)) (Prims.of_int (2))
                    (Prims.of_int (122)) (Prims.of_int (20)))))
           (Obj.magic
              (FStar_Tactics_V2_Derived.apply_lemma
                 (FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_FVar
                       (FStar_Reflection_V2_Builtins.pack_fv
                          ["FStar"; "Tactics"; "BV"; "Lemmas"; "eq_to_bv"])))))
           (fun uu___2 ->
              (fun uu___2 ->
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (120)) (Prims.of_int (2))
                               (Prims.of_int (120)) (Prims.of_int (22)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (121)) (Prims.of_int (2))
                               (Prims.of_int (122)) (Prims.of_int (20)))))
                      (Obj.magic
                         (FStar_Tactics_V2_Derived.apply_lemma
                            (FStar_Reflection_V2_Builtins.pack_ln
                               (FStar_Reflection_V2_Data.Tv_FVar
                                  (FStar_Reflection_V2_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "BV";
                                     "Lemmas";
                                     "trans"])))))
                      (fun uu___3 ->
                         (fun uu___3 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (121))
                                          (Prims.of_int (2))
                                          (Prims.of_int (121))
                                          (Prims.of_int (20)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.BV.fst"
                                          (Prims.of_int (122))
                                          (Prims.of_int (2))
                                          (Prims.of_int (122))
                                          (Prims.of_int (20)))))
                                 (Obj.magic (arith_to_bv_tac ()))
                                 (fun uu___4 ->
                                    (fun uu___4 ->
                                       Obj.magic (arith_to_bv_tac ())) uu___4)))
                           uu___3))) uu___2))
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.BV.to_bv_tac"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.to_bv_tac (plugin)"
               (FStar_Tactics_Native.from_tactic_1 to_bv_tac)
               FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
               psc ncb us args)