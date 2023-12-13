open Prims
let (ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let nm l = FStar_Parser_Const.p2l ["FStar"; "Stubs"; "Pprint"; l] in
  let uu___ =
    let uu___1 = nm "arbitrary_string" in
    FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___1
      FStar_Syntax_Embeddings.e_string FStar_TypeChecker_NBETerm.e_string
      FStar_Syntax_Embeddings.e_document FStar_TypeChecker_NBETerm.e_document
      FStar_Pprint.arbitrary_string in
  let uu___1 =
    let uu___2 =
      let uu___3 = nm "render" in
      FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___3
        FStar_Syntax_Embeddings.e_document
        FStar_TypeChecker_NBETerm.e_document FStar_Syntax_Embeddings.e_string
        FStar_TypeChecker_NBETerm.e_string FStar_Pprint.render in
    [uu___2] in
  uu___ :: uu___1