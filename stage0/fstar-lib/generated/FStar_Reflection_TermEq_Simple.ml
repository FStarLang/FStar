open Prims
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = FStar_Reflection_TermEq.term_eq
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Reflection.TermEq.Simple.term_eq" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.TermEq.Simple.term_eq"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_term
                     FStarC_Reflection_V2_Embeddings.e_term
                     FStarC_Syntax_Embeddings.e_bool term_eq
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.TermEq.Simple.term_eq") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.TermEq.Simple.term_eq"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_term
                   FStarC_Reflection_V2_NBEEmbeddings.e_term
                   FStarC_TypeChecker_NBETerm.e_bool term_eq
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.TermEq.Simple.term_eq") cb us) args))
let (univ_eq :
  FStarC_Reflection_Types.universe ->
    FStarC_Reflection_Types.universe -> Prims.bool)
  = FStar_Reflection_TermEq.univ_eq
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Reflection.TermEq.Simple.univ_eq" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.TermEq.Simple.univ_eq"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_universe
                     FStarC_Reflection_V2_Embeddings.e_universe
                     FStarC_Syntax_Embeddings.e_bool univ_eq
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.TermEq.Simple.univ_eq") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.TermEq.Simple.univ_eq"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_universe
                   FStarC_Reflection_V2_NBEEmbeddings.e_universe
                   FStarC_TypeChecker_NBETerm.e_bool univ_eq
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.TermEq.Simple.univ_eq") cb us) args))