open Fstarcompiler
open Prims
let rec apply_squash_or_lem (d : Prims.nat)
  (t : FStar_Tactics_NamedView.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.try_with
    (fun uu___ -> match () with | () -> FStar_Tactics_V2_Derived.apply t)
    (fun uu___ ->
       FStar_Tactics_V2_Derived.try_with
         (fun uu___1 ->
            match () with
            | () ->
                (fun ps ->
                   FStar_Tactics_V2_Derived.apply
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Squash"; "return_squash"]))) ps;
                   FStar_Tactics_V2_Derived.apply t ps))
         (fun uu___1 ->
            FStar_Tactics_V2_Derived.try_with
              (fun uu___2 ->
                 match () with | () -> FStar_Tactics_V2_Derived.apply_lemma t)
              (fun uu___2 ->
                 if d <= Prims.int_zero
                 then FStar_Tactics_V2_Derived.fail "mapply: out of fuel"
                 else
                   FStar_Tactics_Effect.tac_bind
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (Obj.magic (FStar_Tactics_V2_Derived.cur_env ()))
                           (fun uu___4 ->
                              (fun uu___4 ->
                                 Obj.magic
                                   (FStarC_Tactics_V2_Builtins.tc uu___4 t))
                                uu___4)))
                     (fun uu___4 ->
                        (fun ty ->
                           Obj.magic
                             (fun ps ->
                                let x =
                                  FStar_Tactics_V2_SyntaxHelpers.collect_arr
                                    ty ps in
                                match x with
                                | (tys, c) ->
                                    (match FStar_Tactics_NamedView.inspect_comp
                                             c
                                     with
                                     | FStarC_Reflection_V2_Data.C_Lemma
                                         (pre, post, uu___4) ->
                                         let x1 =
                                           FStarC_Reflection_V2_Builtins.pack_ln
                                             (FStarC_Reflection_V2_Data.Tv_App
                                                (post,
                                                  ((FStarC_Reflection_V2_Builtins.pack_ln
                                                      (FStarC_Reflection_V2_Data.Tv_Const
                                                         FStarC_Reflection_V2_Data.C_Unit)),
                                                    FStarC_Reflection_V2_Data.Q_Explicit))) in
                                         let x2 =
                                           FStar_Tactics_V2_Derived.norm_term
                                             [] x1 ps in
                                         let x3 =
                                           FStar_Reflection_V2_Formula.term_as_formula'
                                             x2 ps in
                                         (match x3 with
                                          | FStar_Reflection_V2_Formula.Implies
                                              (p, q) ->
                                              (FStar_Tactics_V2_Derived.apply_lemma
                                                 (FStarC_Reflection_V2_Builtins.pack_ln
                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                       (FStarC_Reflection_V2_Builtins.pack_fv
                                                          ["FStar";
                                                          "Tactics";
                                                          "MApply0";
                                                          "push1"]))) ps;
                                               apply_squash_or_lem
                                                 (d - Prims.int_one) t ps)
                                          | uu___5 ->
                                              FStar_Tactics_V2_Derived.fail
                                                "mapply: can't apply (1)" ps)
                                     | FStarC_Reflection_V2_Data.C_Total rt
                                         ->
                                         (match FStar_Reflection_V2_Derived.unsquash_term
                                                  rt
                                          with
                                          | FStar_Pervasives_Native.Some rt1
                                              ->
                                              let x1 =
                                                FStar_Tactics_V2_Derived.norm_term
                                                  [] rt1 ps in
                                              let x2 =
                                                FStar_Reflection_V2_Formula.term_as_formula'
                                                  x1 ps in
                                              (match x2 with
                                               | FStar_Reflection_V2_Formula.Implies
                                                   (p, q) ->
                                                   (FStar_Tactics_V2_Derived.apply_lemma
                                                      (FStarC_Reflection_V2_Builtins.pack_ln
                                                         (FStarC_Reflection_V2_Data.Tv_FVar
                                                            (FStarC_Reflection_V2_Builtins.pack_fv
                                                               ["FStar";
                                                               "Tactics";
                                                               "MApply0";
                                                               "push1"]))) ps;
                                                    apply_squash_or_lem
                                                      (d - Prims.int_one) t
                                                      ps)
                                               | uu___4 ->
                                                   FStar_Tactics_V2_Derived.fail
                                                     "mapply: can't apply (2)"
                                                     ps)
                                          | FStar_Pervasives_Native.None ->
                                              let x1 =
                                                FStar_Tactics_V2_Derived.norm_term
                                                  [] rt ps in
                                              let x2 =
                                                FStar_Reflection_V2_Formula.term_as_formula'
                                                  x1 ps in
                                              (match x2 with
                                               | FStar_Reflection_V2_Formula.Implies
                                                   (p, q) ->
                                                   (FStar_Tactics_V2_Derived.apply_lemma
                                                      (FStarC_Reflection_V2_Builtins.pack_ln
                                                         (FStarC_Reflection_V2_Data.Tv_FVar
                                                            (FStarC_Reflection_V2_Builtins.pack_fv
                                                               ["FStar";
                                                               "Tactics";
                                                               "MApply0";
                                                               "push1"]))) ps;
                                                    apply_squash_or_lem
                                                      (d - Prims.int_one) t
                                                      ps)
                                               | uu___4 ->
                                                   (FStar_Tactics_V2_Derived.apply
                                                      (FStarC_Reflection_V2_Builtins.pack_ln
                                                         (FStarC_Reflection_V2_Data.Tv_FVar
                                                            (FStarC_Reflection_V2_Builtins.pack_fv
                                                               ["FStar";
                                                               "Squash";
                                                               "return_squash"])))
                                                      ps;
                                                    FStar_Tactics_V2_Derived.apply
                                                      t ps)))
                                     | uu___4 ->
                                         FStar_Tactics_V2_Derived.fail
                                           "mapply: can't apply (3)" ps)))
                          uu___4))))
let mapply0 (t : FStar_Tactics_NamedView.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  apply_squash_or_lem (Prims.of_int (10)) t
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.MApply0.mapply0" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.MApply0.mapply0 (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 mapply0)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
