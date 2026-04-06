open Fstarcompiler
open Prims
let rec arith_expr_to_bv (e : FStar_Reflection_V2_Arith.expr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  match e with
  | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.MulMod
      (e1, uu___)) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_mul"])))))
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvmul"]))) ps;
                   arith_expr_to_bv e1 ps)) uu___1)
  | FStar_Reflection_V2_Arith.MulMod (e1, uu___) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_mul"])))))
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvmul"]))) ps;
                   arith_expr_to_bv e1 ps)) uu___1)
  | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Umod
      (e1, uu___)) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_mod"])))))
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvmod"]))) ps;
                   arith_expr_to_bv e1 ps)) uu___1)
  | FStar_Reflection_V2_Arith.Umod (e1, uu___) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_mod"])))))
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvmod"]))) ps;
                   arith_expr_to_bv e1 ps)) uu___1)
  | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Udiv
      (e1, uu___)) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_div"])))))
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvdiv"]))) ps;
                   arith_expr_to_bv e1 ps)) uu___1)
  | FStar_Reflection_V2_Arith.Udiv (e1, uu___) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_div"])))))
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvdiv"]))) ps;
                   arith_expr_to_bv e1 ps)) uu___1)
  | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Shl
      (e1, uu___)) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_shl"])))))
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvshl"]))) ps;
                   arith_expr_to_bv e1 ps)) uu___1)
  | FStar_Reflection_V2_Arith.Shl (e1, uu___) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_shl"])))))
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvshl"]))) ps;
                   arith_expr_to_bv e1 ps)) uu___1)
  | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Shr
      (e1, uu___)) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_shr"])))))
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvshr"]))) ps;
                   arith_expr_to_bv e1 ps)) uu___1)
  | FStar_Reflection_V2_Arith.Shr (e1, uu___) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_shr"])))))
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvshr"]))) ps;
                   arith_expr_to_bv e1 ps)) uu___1)
  | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Land
      (e1, e2)) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_logand"])))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvand"]))) ps;
                   arith_expr_to_bv e1 ps;
                   arith_expr_to_bv e2 ps)) uu___)
  | FStar_Reflection_V2_Arith.Land (e1, e2) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_logand"])))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvand"]))) ps;
                   arith_expr_to_bv e1 ps;
                   arith_expr_to_bv e2 ps)) uu___)
  | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Lxor
      (e1, e2)) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_logxor"])))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvxor"]))) ps;
                   arith_expr_to_bv e1 ps;
                   arith_expr_to_bv e2 ps)) uu___)
  | FStar_Reflection_V2_Arith.Lxor (e1, e2) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_logxor"])))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvxor"]))) ps;
                   arith_expr_to_bv e1 ps;
                   arith_expr_to_bv e2 ps)) uu___)
  | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Lor
      (e1, e2)) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_logor"])))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvor"]))) ps;
                   arith_expr_to_bv e1 ps;
                   arith_expr_to_bv e2 ps)) uu___)
  | FStar_Reflection_V2_Arith.Lor (e1, e2) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_logor"])))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvor"]))) ps;
                   arith_expr_to_bv e1 ps;
                   arith_expr_to_bv e2 ps)) uu___)
  | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Ladd
      (e1, e2)) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_add"])))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvadd"]))) ps;
                   arith_expr_to_bv e1 ps;
                   arith_expr_to_bv e2 ps)) uu___)
  | FStar_Reflection_V2_Arith.Ladd (e1, e2) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_add"])))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvadd"]))) ps;
                   arith_expr_to_bv e1 ps;
                   arith_expr_to_bv e2 ps)) uu___)
  | FStar_Reflection_V2_Arith.NatToBv (FStar_Reflection_V2_Arith.Lsub
      (e1, e2)) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_sub"])))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvsub"]))) ps;
                   arith_expr_to_bv e1 ps;
                   arith_expr_to_bv e2 ps)) uu___)
  | FStar_Reflection_V2_Arith.Lsub (e1, e2) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_V2_Derived.apply_lemma
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "BV"; "int2bv_sub"])))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "BV";
                              "Lemmas";
                              "cong_bvsub"]))) ps;
                   arith_expr_to_bv e1 ps;
                   arith_expr_to_bv e2 ps)) uu___)
  | uu___ -> FStar_Tactics_V2_Derived.trefl ()
let arith_to_bv_tac (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.focus
    (fun uu___1 ps ->
       FStarC_Tactics_V2_Builtins.norm
         [Fstarcompiler.FStarC_NormSteps.delta_only ["FStar.BV.bvult"]] ps;
       (let x1 = FStar_Tactics_V2_Derived.cur_goal () ps in
        let x2 = FStar_Reflection_V2_Formula.term_as_formula x1 ps in
        match x2 with
        | FStar_Reflection_V2_Formula.Comp
            (FStar_Reflection_V2_Formula.Eq uu___2, l, r) ->
            let x3 =
              FStar_Reflection_V2_Arith.run_tm
                (FStar_Reflection_V2_Arith.as_arith_expr l) ps in
            (match x3 with
             | Fstarcompiler.FStar_Pervasives.Inl s ->
                 (FStarC_Tactics_V2_Builtins.dump s ps;
                  FStar_Tactics_V2_Derived.trefl () ps)
             | Fstarcompiler.FStar_Pervasives.Inr e ->
                 FStar_Tactics_V2_Derived.seq
                   (fun uu___3 -> arith_expr_to_bv e)
                   FStar_Tactics_V2_Derived.trefl ps)
        | uu___2 ->
            let x3 =
              let x4 = FStarC_Tactics_V2_Builtins.term_to_string x1 ps in
              Prims.strcat "arith_to_bv_tac: unexpected: " x4 in
            FStar_Tactics_V2_Derived.fail x3 ps))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.BV.arith_to_bv_tac" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.arith_to_bv_tac (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  arith_to_bv_tac)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let bv_tac (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.focus
    (fun uu___1 ps ->
       FStar_Tactics_MApply0.mapply0
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_FVar
               (FStarC_Reflection_V2_Builtins.pack_fv
                  ["FStar"; "Tactics"; "BV"; "Lemmas"; "eq_to_bv"]))) ps;
       FStar_Tactics_MApply0.mapply0
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_FVar
               (FStarC_Reflection_V2_Builtins.pack_fv
                  ["FStar"; "Tactics"; "BV"; "Lemmas"; "trans"]))) ps;
       arith_to_bv_tac () ps;
       arith_to_bv_tac () ps;
       FStarC_Tactics_V2_Builtins.set_options "--smtencoding.elim_box true"
         ps;
       FStarC_Tactics_V2_Builtins.norm [Fstarcompiler.FStarC_NormSteps.delta]
         ps;
       FStar_Tactics_V2_Derived.smt () ps)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.BV.bv_tac" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.bv_tac (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 bv_tac)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let bv_tac_lt (n : Prims.int) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.focus
    (fun uu___ ps ->
       let x =
         FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_Const
              (FStarC_Reflection_V2_Data.C_Int n)) in
       let x1 =
         FStar_Reflection_V2_Derived.mk_app
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "BV"; "Lemmas"; "trans_lt2"])))
           [(x, FStarC_Reflection_V2_Data.Q_Implicit)] in
       FStar_Tactics_V2_Derived.apply_lemma x1 ps;
       arith_to_bv_tac () ps;
       arith_to_bv_tac () ps;
       FStarC_Tactics_V2_Builtins.set_options "--smtencoding.elim_box true"
         ps;
       FStar_Tactics_V2_Derived.smt () ps)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.BV.bv_tac_lt" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.bv_tac_lt (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 bv_tac_lt)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let to_bv_tac (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.focus
    (fun uu___1 ps ->
       FStar_Tactics_V2_Derived.apply_lemma
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_FVar
               (FStarC_Reflection_V2_Builtins.pack_fv
                  ["FStar"; "Tactics"; "BV"; "Lemmas"; "eq_to_bv"]))) ps;
       FStar_Tactics_V2_Derived.apply_lemma
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_FVar
               (FStarC_Reflection_V2_Builtins.pack_fv
                  ["FStar"; "Tactics"; "BV"; "Lemmas"; "trans"]))) ps;
       arith_to_bv_tac () ps;
       arith_to_bv_tac () ps)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.BV.to_bv_tac" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.BV.to_bv_tac (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 to_bv_tac)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
