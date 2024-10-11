open Prims
let (ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let nm l = FStarC_Parser_Const.p2l ["FStar"; "Stubs"; "Pprint"; l] in
  let uu___ =
    let uu___1 = nm "arbitrary_string" in
    FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___1
      FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
      FStarC_Syntax_Embeddings.e_document
      FStarC_TypeChecker_NBETerm.e_document FStarC_Pprint.arbitrary_string in
  let uu___1 =
    let uu___2 =
      let uu___3 = nm "render" in
      FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___3
        FStarC_Syntax_Embeddings.e_document
        FStarC_TypeChecker_NBETerm.e_document
        FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
        FStarC_Pprint.render in
    [uu___2] in
  uu___ :: uu___1