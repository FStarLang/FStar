open Prims
let (ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let nm l = FStar_Parser_Const.p2l ["FStar"; "Stubs"; "Errors"; "Msg"; l] in
  let uu___ =
    let uu___1 = nm "text" in
    FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___1
      FStar_Syntax_Embeddings.e_string FStar_TypeChecker_NBETerm.e_string
      FStar_Syntax_Embeddings.e_document FStar_TypeChecker_NBETerm.e_document
      FStar_Errors_Msg.text in
  let uu___1 =
    let uu___2 =
      let uu___3 = nm "sublist" in
      FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___3
        FStar_Syntax_Embeddings.e_document
        FStar_TypeChecker_NBETerm.e_document
        (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_document)
        (FStar_TypeChecker_NBETerm.e_list
           FStar_TypeChecker_NBETerm.e_document)
        FStar_Syntax_Embeddings.e_document
        FStar_TypeChecker_NBETerm.e_document FStar_Errors_Msg.sublist in
    let uu___3 =
      let uu___4 =
        let uu___5 = nm "bulleted" in
        FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___5
          (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_document)
          (FStar_TypeChecker_NBETerm.e_list
             FStar_TypeChecker_NBETerm.e_document)
          FStar_Syntax_Embeddings.e_document
          FStar_TypeChecker_NBETerm.e_document FStar_Errors_Msg.bulleted in
      let uu___5 =
        let uu___6 =
          let uu___7 = nm "mkmsg" in
          FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___7
            FStar_Syntax_Embeddings.e_string
            FStar_TypeChecker_NBETerm.e_string
            (FStar_Syntax_Embeddings.e_list
               FStar_Syntax_Embeddings.e_document)
            (FStar_TypeChecker_NBETerm.e_list
               FStar_TypeChecker_NBETerm.e_document) FStar_Errors_Msg.mkmsg in
        let uu___7 =
          let uu___8 =
            let uu___9 = nm "subdoc" in
            FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___9
              FStar_Syntax_Embeddings.e_document
              FStar_TypeChecker_NBETerm.e_document
              FStar_Syntax_Embeddings.e_document
              FStar_TypeChecker_NBETerm.e_document FStar_Errors_Msg.subdoc in
          let uu___9 =
            let uu___10 =
              let uu___11 = nm "renderdoc" in
              FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___11
                FStar_Syntax_Embeddings.e_document
                FStar_TypeChecker_NBETerm.e_document
                FStar_Syntax_Embeddings.e_string
                FStar_TypeChecker_NBETerm.e_string FStar_Errors_Msg.renderdoc in
            let uu___11 =
              let uu___12 =
                let uu___13 = nm "backtrace_doc" in
                FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___13
                  FStar_Syntax_Embeddings.e_unit
                  FStar_TypeChecker_NBETerm.e_unit
                  FStar_Syntax_Embeddings.e_document
                  FStar_TypeChecker_NBETerm.e_document
                  FStar_Errors_Msg.backtrace_doc in
              let uu___13 =
                let uu___14 =
                  let uu___15 = nm "rendermsg" in
                  FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___15
                    (FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_document)
                    (FStar_TypeChecker_NBETerm.e_list
                       FStar_TypeChecker_NBETerm.e_document)
                    FStar_Syntax_Embeddings.e_string
                    FStar_TypeChecker_NBETerm.e_string
                    FStar_Errors_Msg.rendermsg in
                [uu___14] in
              uu___12 :: uu___13 in
            uu___10 :: uu___11 in
          uu___8 :: uu___9 in
        uu___6 :: uu___7 in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1