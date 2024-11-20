open Prims
type proposition = FStarC_Reflection_Types.term
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = FStar_Reflection_TermEq_Simple.term_eq
let (proposition_to_string :
  proposition -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun p -> FStarC_Tactics_V1_Builtins.term_to_string p
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.Propositions.proposition_to_string"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.InteractiveHelpers.Propositions.proposition_to_string (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 proposition_to_string)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_string psc ncb us args)
type assertions =
  {
  pres: proposition Prims.list ;
  posts: proposition Prims.list }
let rec __knot_e_assertions _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.InteractiveHelpers.Propositions.assertions"
    (fun tm_0 ->
       match tm_0 with
       | ("FStar.InteractiveHelpers.Propositions.Mkassertions",
          pres_2::posts_3::[]) ->
           FStarC_Compiler_Util.bind_opt
             (FStarC_Syntax_Embeddings_Base.extracted_unembed
                (FStarC_Syntax_Embeddings.e_list
                   FStarC_Reflection_V2_Embeddings.e_term) pres_2)
             (fun pres_2 ->
                FStarC_Compiler_Util.bind_opt
                  (FStarC_Syntax_Embeddings_Base.extracted_unembed
                     (FStarC_Syntax_Embeddings.e_list
                        FStarC_Reflection_V2_Embeddings.e_term) posts_3)
                  (fun posts_3 ->
                     FStar_Pervasives_Native.Some
                       { pres = pres_2; posts = posts_3 }))
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_4 ->
       match tm_4 with
       | { pres = pres_6; posts = posts_7;_} ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str
                   "FStar.InteractiveHelpers.Propositions.Mkassertions"))
             [((FStarC_Syntax_Embeddings_Base.extracted_embed
                  (FStarC_Syntax_Embeddings.e_list
                     FStarC_Reflection_V2_Embeddings.e_term) pres_6),
                FStar_Pervasives_Native.None);
             ((FStarC_Syntax_Embeddings_Base.extracted_embed
                 (FStarC_Syntax_Embeddings.e_list
                    FStarC_Reflection_V2_Embeddings.e_term) posts_7),
               FStar_Pervasives_Native.None)])
let e_assertions = __knot_e_assertions ()
let (__proj__Mkassertions__item__pres : assertions -> proposition Prims.list)
  = fun projectee -> match projectee with | { pres; posts;_} -> pres
let (__proj__Mkassertions__item__posts :
  assertions -> proposition Prims.list) =
  fun projectee -> match projectee with | { pres; posts;_} -> posts
let (mk_assertions :
  proposition Prims.list -> proposition Prims.list -> assertions) =
  fun pres -> fun posts -> { pres; posts }
let (simpl_norm_steps : FStar_Pervasives.norm_step Prims.list) =
  [FStar_Pervasives.primops;
  FStar_Pervasives.simplify;
  FStar_Pervasives.iota]
let (is_trivial_proposition :
  proposition -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun p ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               term_eq
                 (FStarC_Reflection_V2_Builtins.pack_ln
                    (FStarC_Reflection_V2_Data.Tv_FVar
                       (FStarC_Reflection_V2_Builtins.pack_fv
                          ["Prims"; "l_True"]))) p))) uu___
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.Propositions.is_trivial_proposition"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.InteractiveHelpers.Propositions.is_trivial_proposition (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 is_trivial_proposition)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_bool psc ncb us args)
let (simp_filter_proposition :
  FStarC_Reflection_Types.env ->
    FStar_Pervasives.norm_step Prims.list ->
      proposition ->
        (proposition Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun steps ->
      fun p ->
        let uu___ = FStarC_Tactics_V1_Builtins.norm_term_env e steps p in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Propositions.fst"
                   (Prims.of_int (31)) (Prims.of_int (14))
                   (Prims.of_int (31)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Propositions.fst"
                   (Prims.of_int (33)) (Prims.of_int (2)) (Prims.of_int (34))
                   (Prims.of_int (14))))) (Obj.magic uu___)
          (fun prop1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  if
                    term_eq
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["Prims"; "l_True"]))) prop1
                  then []
                  else [prop1]))
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.Propositions.simp_filter_proposition"
    (Prims.of_int (4))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_3
               "FStar.InteractiveHelpers.Propositions.simp_filter_proposition (plugin)"
               (FStarC_Tactics_Native.from_tactic_3 simp_filter_proposition)
               FStarC_Reflection_V2_Embeddings.e_env
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Syntax_Embeddings.e_norm_step)
               FStarC_Reflection_V2_Embeddings.e_term
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_term) psc ncb us args)
let (simp_filter_propositions :
  FStarC_Reflection_Types.env ->
    FStar_Pervasives.norm_step Prims.list ->
      proposition Prims.list ->
        (proposition Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun steps ->
      fun pl ->
        let uu___ =
          FStar_Tactics_Util.map (simp_filter_proposition e steps) pl in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Propositions.fst"
                   (Prims.of_int (38)) (Prims.of_int (19))
                   (Prims.of_int (38)) (Prims.of_int (61)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Propositions.fst"
                   (Prims.of_int (38)) (Prims.of_int (2)) (Prims.of_int (38))
                   (Prims.of_int (61))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> FStar_List_Tot_Base.flatten uu___1))
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.Propositions.simp_filter_propositions"
    (Prims.of_int (4))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_3
               "FStar.InteractiveHelpers.Propositions.simp_filter_propositions (plugin)"
               (FStarC_Tactics_Native.from_tactic_3 simp_filter_propositions)
               FStarC_Reflection_V2_Embeddings.e_env
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Syntax_Embeddings.e_norm_step)
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_term)
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_term) psc ncb us args)
let (simp_filter_assertions :
  FStarC_Reflection_Types.env ->
    FStar_Pervasives.norm_step Prims.list ->
      assertions -> (assertions, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun steps ->
      fun a ->
        let uu___ = simp_filter_propositions e steps a.pres in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Propositions.fst"
                   (Prims.of_int (42)) (Prims.of_int (13))
                   (Prims.of_int (42)) (Prims.of_int (52)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Propositions.fst"
                   (Prims.of_int (42)) (Prims.of_int (55))
                   (Prims.of_int (44)) (Prims.of_int (26)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun pres ->
                let uu___1 = simp_filter_propositions e steps a.posts in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Propositions.fst"
                              (Prims.of_int (43)) (Prims.of_int (14))
                              (Prims.of_int (43)) (Prims.of_int (54)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Propositions.fst"
                              (Prims.of_int (44)) (Prims.of_int (2))
                              (Prims.of_int (44)) (Prims.of_int (26)))))
                     (Obj.magic uu___1)
                     (fun posts ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> mk_assertions pres posts)))) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.Propositions.simp_filter_assertions"
    (Prims.of_int (4))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_3
               "FStar.InteractiveHelpers.Propositions.simp_filter_assertions (plugin)"
               (FStarC_Tactics_Native.from_tactic_3 simp_filter_assertions)
               FStarC_Reflection_V2_Embeddings.e_env
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Syntax_Embeddings.e_norm_step) e_assertions
               e_assertions psc ncb us args)