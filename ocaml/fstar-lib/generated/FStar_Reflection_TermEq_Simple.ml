open Prims
let (term_eq :
  FStar_Reflection_Types.term -> FStar_Reflection_Types.term -> Prims.bool) =
  FStar_Reflection_TermEq.term_eq
let _ =
  FStar_Tactics_Native.register_plugin
    "FStar.Reflection.TermEq.Simple.term_eq" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStar_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.TermEq.Simple.term_eq"
               (fun _ ->
                  (FStar_Syntax_Embeddings.arrow_as_prim_step_2
                     FStar_Reflection_V2_Embeddings.e_term
                     FStar_Reflection_V2_Embeddings.e_term
                     FStar_Syntax_Embeddings.e_bool term_eq Prims.int_zero
                     (FStar_Ident.lid_of_str
                        "FStar.Reflection.TermEq.Simple.term_eq") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStar_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.TermEq.Simple.term_eq"
             (fun _ ->
                (FStar_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStar_Reflection_V2_NBEEmbeddings.e_term
                   FStar_Reflection_V2_NBEEmbeddings.e_term
                   FStar_TypeChecker_NBETerm.e_bool term_eq Prims.int_zero
                   (FStar_Ident.lid_of_str
                      "FStar.Reflection.TermEq.Simple.term_eq") cb us) args))
let (univ_eq :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe -> Prims.bool)
  = FStar_Reflection_TermEq.univ_eq
let _ =
  FStar_Tactics_Native.register_plugin
    "FStar.Reflection.TermEq.Simple.univ_eq" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStar_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.TermEq.Simple.univ_eq"
               (fun _ ->
                  (FStar_Syntax_Embeddings.arrow_as_prim_step_2
                     FStar_Reflection_V2_Embeddings.e_universe
                     FStar_Reflection_V2_Embeddings.e_universe
                     FStar_Syntax_Embeddings.e_bool univ_eq Prims.int_zero
                     (FStar_Ident.lid_of_str
                        "FStar.Reflection.TermEq.Simple.univ_eq") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStar_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.TermEq.Simple.univ_eq"
             (fun _ ->
                (FStar_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStar_Reflection_V2_NBEEmbeddings.e_universe
                   FStar_Reflection_V2_NBEEmbeddings.e_universe
                   FStar_TypeChecker_NBETerm.e_bool univ_eq Prims.int_zero
                   (FStar_Ident.lid_of_str
                      "FStar.Reflection.TermEq.Simple.univ_eq") cb us) args))