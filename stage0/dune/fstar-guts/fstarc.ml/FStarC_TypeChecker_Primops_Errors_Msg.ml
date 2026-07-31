open Prims
let ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  let nm l = FStarC_Parser_Const.p2l ["FStar"; "Errors"; "Msg"; l] in
  let uu___ =
    let uu___1 = nm "text" in
    FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___1
      FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
      FStarC_Syntax_Embeddings.e_document
      FStarC_TypeChecker_NBETerm.e_document FStarC_Errors_Msg.text in
  let uu___1 =
    let uu___2 =
      let uu___3 = nm "mkmsg" in
      FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___3
        FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
        (FStarC_Syntax_Embeddings.e_list FStarC_Syntax_Embeddings.e_document)
        (FStarC_TypeChecker_NBETerm.e_list
           FStarC_TypeChecker_NBETerm.e_document) FStarC_Errors_Msg.mkmsg in
    [uu___2] in
  uu___ :: uu___1
