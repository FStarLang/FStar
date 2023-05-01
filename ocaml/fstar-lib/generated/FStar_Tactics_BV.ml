open Prims
let rec (arith_expr_to_bv :
  FStar_Reflection_Arith.expr -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    match e with
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.MulMod
        (e1, uu___)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (113))
             (Prims.of_int (8)) (Prims.of_int (113)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (114))
             (Prims.of_int (8)) (Prims.of_int (115)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_mul"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (114)) (Prims.of_int (8))
                        (Prims.of_int (114)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (115)) (Prims.of_int (8))
                        (Prims.of_int (115)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvmul"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_Arith.MulMod (e1, uu___) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (113))
             (Prims.of_int (8)) (Prims.of_int (113)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (114))
             (Prims.of_int (8)) (Prims.of_int (115)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_mul"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (114)) (Prims.of_int (8))
                        (Prims.of_int (114)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (115)) (Prims.of_int (8))
                        (Prims.of_int (115)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvmul"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Umod
        (e1, uu___)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (117))
             (Prims.of_int (8)) (Prims.of_int (117)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (118))
             (Prims.of_int (8)) (Prims.of_int (119)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_mod"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (118)) (Prims.of_int (8))
                        (Prims.of_int (118)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (119)) (Prims.of_int (8))
                        (Prims.of_int (119)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvmod"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_Arith.Umod (e1, uu___) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (117))
             (Prims.of_int (8)) (Prims.of_int (117)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (118))
             (Prims.of_int (8)) (Prims.of_int (119)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_mod"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (118)) (Prims.of_int (8))
                        (Prims.of_int (118)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (119)) (Prims.of_int (8))
                        (Prims.of_int (119)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvmod"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Udiv
        (e1, uu___)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (121))
             (Prims.of_int (8)) (Prims.of_int (121)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (122))
             (Prims.of_int (8)) (Prims.of_int (123)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_div"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (122)) (Prims.of_int (8))
                        (Prims.of_int (122)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (123)) (Prims.of_int (8))
                        (Prims.of_int (123)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvdiv"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_Arith.Udiv (e1, uu___) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (121))
             (Prims.of_int (8)) (Prims.of_int (121)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (122))
             (Prims.of_int (8)) (Prims.of_int (123)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_div"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (122)) (Prims.of_int (8))
                        (Prims.of_int (122)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (123)) (Prims.of_int (8))
                        (Prims.of_int (123)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvdiv"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Shl (e1, uu___))
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (125))
             (Prims.of_int (8)) (Prims.of_int (125)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (126))
             (Prims.of_int (8)) (Prims.of_int (127)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_shl"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (126)) (Prims.of_int (8))
                        (Prims.of_int (126)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (127)) (Prims.of_int (8))
                        (Prims.of_int (127)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvshl"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_Arith.Shl (e1, uu___) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (125))
             (Prims.of_int (8)) (Prims.of_int (125)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (126))
             (Prims.of_int (8)) (Prims.of_int (127)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_shl"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (126)) (Prims.of_int (8))
                        (Prims.of_int (126)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (127)) (Prims.of_int (8))
                        (Prims.of_int (127)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvshl"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Shr (e1, uu___))
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (129))
             (Prims.of_int (8)) (Prims.of_int (129)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (130))
             (Prims.of_int (8)) (Prims.of_int (131)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_shr"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (130)) (Prims.of_int (8))
                        (Prims.of_int (130)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (131)) (Prims.of_int (8))
                        (Prims.of_int (131)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvshr"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_Arith.Shr (e1, uu___) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (129))
             (Prims.of_int (8)) (Prims.of_int (129)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (130))
             (Prims.of_int (8)) (Prims.of_int (131)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_shr"])))))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (130)) (Prims.of_int (8))
                        (Prims.of_int (130)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (131)) (Prims.of_int (8))
                        (Prims.of_int (131)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvshr"])))))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (arith_expr_to_bv e1))
                          uu___2))) uu___1)
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Land (e1, e2))
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (133))
             (Prims.of_int (8)) (Prims.of_int (133)) (Prims.of_int (36)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (134))
             (Prims.of_int (8)) (Prims.of_int (136)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logand"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (134)) (Prims.of_int (8))
                        (Prims.of_int (134)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (135)) (Prims.of_int (8))
                        (Prims.of_int (136)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvand"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (135)) (Prims.of_int (8))
                                   (Prims.of_int (135)) (Prims.of_int (27)))
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (136)) (Prims.of_int (8))
                                   (Prims.of_int (136)) (Prims.of_int (27)))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_Arith.Land (e1, e2) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (133))
             (Prims.of_int (8)) (Prims.of_int (133)) (Prims.of_int (36)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (134))
             (Prims.of_int (8)) (Prims.of_int (136)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logand"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (134)) (Prims.of_int (8))
                        (Prims.of_int (134)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (135)) (Prims.of_int (8))
                        (Prims.of_int (136)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvand"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (135)) (Prims.of_int (8))
                                   (Prims.of_int (135)) (Prims.of_int (27)))
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (136)) (Prims.of_int (8))
                                   (Prims.of_int (136)) (Prims.of_int (27)))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Lxor (e1, e2))
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (138))
             (Prims.of_int (8)) (Prims.of_int (138)) (Prims.of_int (36)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (139))
             (Prims.of_int (8)) (Prims.of_int (141)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logxor"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (139)) (Prims.of_int (8))
                        (Prims.of_int (139)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (140)) (Prims.of_int (8))
                        (Prims.of_int (141)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvxor"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (140)) (Prims.of_int (8))
                                   (Prims.of_int (140)) (Prims.of_int (27)))
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (141)) (Prims.of_int (8))
                                   (Prims.of_int (141)) (Prims.of_int (27)))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_Arith.Lxor (e1, e2) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (138))
             (Prims.of_int (8)) (Prims.of_int (138)) (Prims.of_int (36)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (139))
             (Prims.of_int (8)) (Prims.of_int (141)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logxor"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (139)) (Prims.of_int (8))
                        (Prims.of_int (139)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (140)) (Prims.of_int (8))
                        (Prims.of_int (141)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvxor"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (140)) (Prims.of_int (8))
                                   (Prims.of_int (140)) (Prims.of_int (27)))
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (141)) (Prims.of_int (8))
                                   (Prims.of_int (141)) (Prims.of_int (27)))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Lor (e1, e2)) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (143))
             (Prims.of_int (8)) (Prims.of_int (143)) (Prims.of_int (35)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (144))
             (Prims.of_int (8)) (Prims.of_int (146)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logor"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (144)) (Prims.of_int (8))
                        (Prims.of_int (144)) (Prims.of_int (32)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (145)) (Prims.of_int (8))
                        (Prims.of_int (146)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvor"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (145)) (Prims.of_int (8))
                                   (Prims.of_int (145)) (Prims.of_int (27)))
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (146)) (Prims.of_int (8))
                                   (Prims.of_int (146)) (Prims.of_int (27)))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_Arith.Lor (e1, e2) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (143))
             (Prims.of_int (8)) (Prims.of_int (143)) (Prims.of_int (35)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (144))
             (Prims.of_int (8)) (Prims.of_int (146)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_logor"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (144)) (Prims.of_int (8))
                        (Prims.of_int (144)) (Prims.of_int (32)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (145)) (Prims.of_int (8))
                        (Prims.of_int (146)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvor"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (145)) (Prims.of_int (8))
                                   (Prims.of_int (145)) (Prims.of_int (27)))
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (146)) (Prims.of_int (8))
                                   (Prims.of_int (146)) (Prims.of_int (27)))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Ladd (e1, e2))
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (148))
             (Prims.of_int (8)) (Prims.of_int (148)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (149))
             (Prims.of_int (8)) (Prims.of_int (151)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_add"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (149)) (Prims.of_int (8))
                        (Prims.of_int (149)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (150)) (Prims.of_int (8))
                        (Prims.of_int (151)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvadd"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (150)) (Prims.of_int (8))
                                   (Prims.of_int (150)) (Prims.of_int (27)))
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (151)) (Prims.of_int (8))
                                   (Prims.of_int (151)) (Prims.of_int (27)))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_Arith.Ladd (e1, e2) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (148))
             (Prims.of_int (8)) (Prims.of_int (148)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (149))
             (Prims.of_int (8)) (Prims.of_int (151)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_add"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (149)) (Prims.of_int (8))
                        (Prims.of_int (149)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (150)) (Prims.of_int (8))
                        (Prims.of_int (151)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvadd"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (150)) (Prims.of_int (8))
                                   (Prims.of_int (150)) (Prims.of_int (27)))
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (151)) (Prims.of_int (8))
                                   (Prims.of_int (151)) (Prims.of_int (27)))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Lsub (e1, e2))
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (153))
             (Prims.of_int (8)) (Prims.of_int (153)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (154))
             (Prims.of_int (8)) (Prims.of_int (156)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_sub"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (154)) (Prims.of_int (8))
                        (Prims.of_int (154)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (155)) (Prims.of_int (8))
                        (Prims.of_int (156)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvsub"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (155)) (Prims.of_int (8))
                                   (Prims.of_int (155)) (Prims.of_int (27)))
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (156)) (Prims.of_int (8))
                                   (Prims.of_int (156)) (Prims.of_int (27)))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | FStar_Reflection_Arith.Lsub (e1, e2) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (153))
             (Prims.of_int (8)) (Prims.of_int (153)) (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (154))
             (Prims.of_int (8)) (Prims.of_int (156)) (Prims.of_int (27)))
          (Obj.magic
             (FStar_Tactics_Derived.apply_lemma
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_FVar
                      (FStar_Reflection_Builtins.pack_fv
                         ["FStar"; "BV"; "int2bv_sub"])))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (154)) (Prims.of_int (8))
                        (Prims.of_int (154)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                        (Prims.of_int (155)) (Prims.of_int (8))
                        (Prims.of_int (156)) (Prims.of_int (27)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "BV"; "cong_bvsub"])))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (155)) (Prims.of_int (8))
                                   (Prims.of_int (155)) (Prims.of_int (27)))
                                (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                   (Prims.of_int (156)) (Prims.of_int (8))
                                   (Prims.of_int (156)) (Prims.of_int (27)))
                                (Obj.magic (arith_expr_to_bv e1))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic (arith_expr_to_bv e2)) uu___2)))
                          uu___1))) uu___)
    | uu___ -> FStar_Tactics_Derived.trefl ()
let (arith_to_bv_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Derived.focus
      (fun uu___1 ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (161))
              (Prims.of_int (4)) (Prims.of_int (161)) (Prims.of_int (40)))
           (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (162))
              (Prims.of_int (4)) (Prims.of_int (175)) (Prims.of_int (65)))
           (Obj.magic
              (FStar_Tactics_Builtins.norm
                 [FStar_Pervasives.delta_only ["FStar.BV.bvult"]]))
           (fun uu___2 ->
              (fun uu___2 ->
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                         (Prims.of_int (162)) (Prims.of_int (12))
                         (Prims.of_int (162)) (Prims.of_int (23)))
                      (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                         (Prims.of_int (163)) (Prims.of_int (4))
                         (Prims.of_int (175)) (Prims.of_int (65)))
                      (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                      (fun uu___3 ->
                         (fun g ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                    (Prims.of_int (163)) (Prims.of_int (12))
                                    (Prims.of_int (163)) (Prims.of_int (29)))
                                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                    (Prims.of_int (164)) (Prims.of_int (4))
                                    (Prims.of_int (175)) (Prims.of_int (65)))
                                 (Obj.magic
                                    (FStar_Reflection_Formula.term_as_formula
                                       g))
                                 (fun uu___3 ->
                                    (fun f ->
                                       match f with
                                       | FStar_Reflection_Formula.Comp
                                           (FStar_Reflection_Formula.Eq
                                            uu___3, l, r)
                                           ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (166))
                                                   (Prims.of_int (17))
                                                   (Prims.of_int (166))
                                                   (Prims.of_int (41)))
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (166))
                                                   (Prims.of_int (11))
                                                   (Prims.of_int (172))
                                                   (Prims.of_int (52)))
                                                (Obj.magic
                                                   (FStar_Reflection_Arith.run_tm
                                                      (FStar_Reflection_Arith.as_arith_expr
                                                         l)))
                                                (fun uu___4 ->
                                                   (fun uu___4 ->
                                                      match uu___4 with
                                                      | FStar_Pervasives.Inl
                                                          s ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.BV.fst"
                                                                  (Prims.of_int (168))
                                                                  (Prims.of_int (10))
                                                                  (Prims.of_int (168))
                                                                  (Prims.of_int (16)))
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.BV.fst"
                                                                  (Prims.of_int (169))
                                                                  (Prims.of_int (10))
                                                                  (Prims.of_int (169))
                                                                  (Prims.of_int (18)))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Builtins.dump
                                                                    s))
                                                               (fun uu___5 ->
                                                                  (fun uu___5
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Derived.trefl
                                                                    ()))
                                                                    uu___5))
                                                      | FStar_Pervasives.Inr
                                                          e ->
                                                          Obj.magic
                                                            (FStar_Tactics_Derived.seq
                                                               (fun uu___5 ->
                                                                  arith_expr_to_bv
                                                                    e)
                                                               FStar_Tactics_Derived.trefl))
                                                     uu___4))
                                       | uu___3 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (175))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (175))
                                                   (Prims.of_int (65)))
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (175))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (175))
                                                   (Prims.of_int (65)))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (175))
                                                         (Prims.of_int (48))
                                                         (Prims.of_int (175))
                                                         (Prims.of_int (64)))
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))
                                                      (Obj.magic
                                                         (FStar_Tactics_Builtins.term_to_string
                                                            g))
                                                      (fun uu___4 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___5 ->
                                                              Prims.strcat
                                                                "arith_to_bv_tac: unexpected: "
                                                                uu___4))))
                                                (fun uu___4 ->
                                                   FStar_Tactics_Derived.fail
                                                     uu___4))) uu___3)))
                           uu___3))) uu___2))
let (bv_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Derived.focus
      (fun uu___1 ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (182))
              (Prims.of_int (2)) (Prims.of_int (182)) (Prims.of_int (20)))
           (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (183))
              (Prims.of_int (2)) (Prims.of_int (188)) (Prims.of_int (8)))
           (Obj.magic
              (FStar_Tactics_Derived.mapply
                 (FStar_Reflection_Builtins.pack_ln
                    (FStar_Reflection_Data.Tv_FVar
                       (FStar_Reflection_Builtins.pack_fv
                          ["FStar"; "Tactics"; "BV"; "eq_to_bv"])))))
           (fun uu___2 ->
              (fun uu___2 ->
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                         (Prims.of_int (183)) (Prims.of_int (2))
                         (Prims.of_int (183)) (Prims.of_int (17)))
                      (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                         (Prims.of_int (184)) (Prims.of_int (2))
                         (Prims.of_int (188)) (Prims.of_int (8)))
                      (Obj.magic
                         (FStar_Tactics_Derived.mapply
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar"; "Tactics"; "BV"; "trans"])))))
                      (fun uu___3 ->
                         (fun uu___3 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                    (Prims.of_int (184)) (Prims.of_int (2))
                                    (Prims.of_int (184)) (Prims.of_int (20)))
                                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                    (Prims.of_int (185)) (Prims.of_int (2))
                                    (Prims.of_int (188)) (Prims.of_int (8)))
                                 (Obj.magic (arith_to_bv_tac ()))
                                 (fun uu___4 ->
                                    (fun uu___4 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (185))
                                               (Prims.of_int (2))
                                               (Prims.of_int (185))
                                               (Prims.of_int (20)))
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (186))
                                               (Prims.of_int (2))
                                               (Prims.of_int (188))
                                               (Prims.of_int (8)))
                                            (Obj.magic (arith_to_bv_tac ()))
                                            (fun uu___5 ->
                                               (fun uu___5 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.BV.fst"
                                                          (Prims.of_int (186))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (186))
                                                          (Prims.of_int (43)))
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.BV.fst"
                                                          (Prims.of_int (187))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (188))
                                                          (Prims.of_int (8)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Builtins.set_options
                                                             "--smtencoding.elim_box true"))
                                                       (fun uu___6 ->
                                                          (fun uu___6 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (14)))
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (8)))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Builtins.norm
                                                                    [FStar_Pervasives.delta]))
                                                                  (fun uu___7
                                                                    ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Derived.smt
                                                                    ()))
                                                                    uu___7)))
                                                            uu___6))) uu___5)))
                                      uu___4))) uu___3))) uu___2))
let (bv_tac_lt : Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun n ->
    FStar_Tactics_Derived.focus
      (fun uu___ ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (192))
              (Prims.of_int (11)) (Prims.of_int (192)) (Prims.of_int (39)))
           (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (193))
              (Prims.of_int (2)) (Prims.of_int (198)) (Prims.of_int (8)))
           (FStar_Tactics_Effect.lift_div_tac
              (fun uu___1 ->
                 FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_Const
                      (FStar_Reflection_Data.C_Int n))))
           (fun uu___1 ->
              (fun nn ->
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                         (Prims.of_int (193)) (Prims.of_int (10))
                         (Prims.of_int (193)) (Prims.of_int (48)))
                      (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                         (Prims.of_int (194)) (Prims.of_int (2))
                         (Prims.of_int (198)) (Prims.of_int (8)))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            FStar_Reflection_Derived.mk_app
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "trans_lt2"])))
                              [(nn, FStar_Reflection_Data.Q_Implicit)]))
                      (fun uu___1 ->
                         (fun t ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                    (Prims.of_int (194)) (Prims.of_int (2))
                                    (Prims.of_int (194)) (Prims.of_int (15)))
                                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                    (Prims.of_int (195)) (Prims.of_int (2))
                                    (Prims.of_int (198)) (Prims.of_int (8)))
                                 (Obj.magic
                                    (FStar_Tactics_Derived.apply_lemma t))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (195))
                                               (Prims.of_int (2))
                                               (Prims.of_int (195))
                                               (Prims.of_int (20)))
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (196))
                                               (Prims.of_int (2))
                                               (Prims.of_int (198))
                                               (Prims.of_int (8)))
                                            (Obj.magic (arith_to_bv_tac ()))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.BV.fst"
                                                          (Prims.of_int (196))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (196))
                                                          (Prims.of_int (20)))
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.BV.fst"
                                                          (Prims.of_int (197))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (198))
                                                          (Prims.of_int (8)))
                                                       (Obj.magic
                                                          (arith_to_bv_tac ()))
                                                       (fun uu___3 ->
                                                          (fun uu___3 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (43)))
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (8)))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Builtins.set_options
                                                                    "--smtencoding.elim_box true"))
                                                                  (fun uu___4
                                                                    ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Derived.smt
                                                                    ()))
                                                                    uu___4)))
                                                            uu___3))) uu___2)))
                                      uu___1))) uu___1))) uu___1))
let (to_bv_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Derived.focus
      (fun uu___1 ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (202))
              (Prims.of_int (2)) (Prims.of_int (202)) (Prims.of_int (25)))
           (FStar_Range.mk_range "FStar.Tactics.BV.fst" (Prims.of_int (203))
              (Prims.of_int (2)) (Prims.of_int (205)) (Prims.of_int (20)))
           (Obj.magic
              (FStar_Tactics_Derived.apply_lemma
                 (FStar_Reflection_Builtins.pack_ln
                    (FStar_Reflection_Data.Tv_FVar
                       (FStar_Reflection_Builtins.pack_fv
                          ["FStar"; "Tactics"; "BV"; "eq_to_bv"])))))
           (fun uu___2 ->
              (fun uu___2 ->
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                         (Prims.of_int (203)) (Prims.of_int (2))
                         (Prims.of_int (203)) (Prims.of_int (22)))
                      (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                         (Prims.of_int (204)) (Prims.of_int (2))
                         (Prims.of_int (205)) (Prims.of_int (20)))
                      (Obj.magic
                         (FStar_Tactics_Derived.apply_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar"; "Tactics"; "BV"; "trans"])))))
                      (fun uu___3 ->
                         (fun uu___3 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                    (Prims.of_int (204)) (Prims.of_int (2))
                                    (Prims.of_int (204)) (Prims.of_int (20)))
                                 (FStar_Range.mk_range "FStar.Tactics.BV.fst"
                                    (Prims.of_int (205)) (Prims.of_int (2))
                                    (Prims.of_int (205)) (Prims.of_int (20)))
                                 (Obj.magic (arith_to_bv_tac ()))
                                 (fun uu___4 ->
                                    (fun uu___4 ->
                                       Obj.magic (arith_to_bv_tac ())) uu___4)))
                           uu___3))) uu___2))
