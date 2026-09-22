open Prims
let rec apply_squash_or_lem (d : Prims.nat)
  (t : FStar_Tactics_NamedView.term) :
  FStarC_Tactics_Types.ref_proofstate -> unit=
  FStar_Tactics_V2_Derived.try_with
    (fun uu___ -> match () with | () -> FStar_Tactics_V2_Derived.apply t)
    (fun uu___ ->
       FStar_Tactics_V2_Derived.try_with
         (fun uu___1 ->
            match () with | () -> FStar_Tactics_V2_Derived.apply_lemma t)
         (fun uu___1 ->
            if d <= Prims.int_zero
            then FStar_Tactics_V2_Derived.fail "mapply: out of fuel"
            else
              (fun ps ->
                 let x =
                   let x1 = FStar_Tactics_V2_Derived.cur_env () ps in
                   FStarC_Tactics_V2_Builtins.tc x1 t ps in
                 let x1 = FStar_Tactics_V2_SyntaxHelpers.collect_arr x ps in
                 match x1 with
                 | (tys, c) ->
                     let x2 = FStar_Tactics_NamedView.inspect_comp c in
                     if Prims.not (FStarC_Reflection_V2_Data.is_tot_comp x2)
                     then
                       FStar_Tactics_V2_Derived.fail
                         "mapply: can't apply (3)" ps
                     else
                       (let x3 = x2.FStarC_Reflection_V2_Data.result_typ in
                        match FStar_Reflection_V2_Derived.unsquash_term x3
                        with
                        | FStar_Pervasives_Native.Some rt ->
                            let x4 =
                              FStar_Tactics_V2_Derived.norm_term [] rt ps in
                            let x5 =
                              FStar_Reflection_V2_Formula.term_as_formula' x4
                                ps in
                            (match x5 with
                             | FStar_Reflection_V2_Formula.Implies (p, q) ->
                                 (FStar_Tactics_V2_Derived.apply_lemma
                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                       (FStarC_Reflection_V2_Data.Tv_FVar
                                          (FStarC_Reflection_V2_Builtins.pack_fv
                                             ["FStar";
                                             "Tactics";
                                             "MApply0";
                                             "push1"]))) ps;
                                  apply_squash_or_lem (d - Prims.int_one) t
                                    ps)
                             | uu___2 ->
                                 FStar_Tactics_V2_Derived.fail
                                   "mapply: can't apply (2)" ps)
                        | FStar_Pervasives_Native.None ->
                            let x4 =
                              FStar_Tactics_V2_Derived.norm_term [] x3 ps in
                            let x5 =
                              FStar_Reflection_V2_Formula.term_as_formula' x4
                                ps in
                            (match x5 with
                             | FStar_Reflection_V2_Formula.Implies (p, q) ->
                                 (FStar_Tactics_V2_Derived.apply_lemma
                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                       (FStarC_Reflection_V2_Data.Tv_FVar
                                          (FStarC_Reflection_V2_Builtins.pack_fv
                                             ["FStar";
                                             "Tactics";
                                             "MApply0";
                                             "push1"]))) ps;
                                  apply_squash_or_lem (d - Prims.int_one) t
                                    ps)
                             | uu___2 -> FStar_Tactics_V2_Derived.apply t ps)))))
let mapply0 (t : FStar_Tactics_NamedView.term) :
  FStarC_Tactics_Types.ref_proofstate -> unit=
  apply_squash_or_lem (Prims.of_int 10) t
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.MApply0.mapply0"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.MApply0.mapply0 (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 mapply0)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
