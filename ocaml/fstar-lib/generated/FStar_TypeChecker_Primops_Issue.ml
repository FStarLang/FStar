open Prims
let (ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let mk_lid l = FStar_Parser_Const.p2l ["FStar"; "Issue"; l] in
  let uu___ =
    let uu___1 = mk_lid "message_of_issue" in
    FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___1
      FStar_Syntax_Embeddings.e_issue FStar_TypeChecker_NBETerm.e_issue
      (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_document)
      (FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_document)
      FStar_Errors.__proj__Mkissue__item__issue_msg in
  let uu___1 =
    let uu___2 =
      let uu___3 = mk_lid "level_of_issue" in
      FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___3
        FStar_Syntax_Embeddings.e_issue FStar_TypeChecker_NBETerm.e_issue
        FStar_Syntax_Embeddings.e_string FStar_TypeChecker_NBETerm.e_string
        (fun i ->
           FStar_Errors.string_of_issue_level i.FStar_Errors.issue_level) in
    let uu___3 =
      let uu___4 =
        let uu___5 = mk_lid "number_of_issue" in
        FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___5
          FStar_Syntax_Embeddings.e_issue FStar_TypeChecker_NBETerm.e_issue
          (FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_int)
          (FStar_TypeChecker_NBETerm.e_option FStar_TypeChecker_NBETerm.e_int)
          (fun uu___6 ->
             (fun i ->
                Obj.magic
                  (FStar_Class_Monad.fmap FStar_Class_Monad.monad_option ()
                     ()
                     (fun uu___6 -> (Obj.magic FStar_BigInt.of_int_fs) uu___6)
                     (Obj.magic i.FStar_Errors.issue_number))) uu___6) in
      let uu___5 =
        let uu___6 =
          let uu___7 = mk_lid "range_of_issue" in
          FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___7
            FStar_Syntax_Embeddings.e_issue FStar_TypeChecker_NBETerm.e_issue
            (FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_range)
            (FStar_TypeChecker_NBETerm.e_option
               FStar_TypeChecker_NBETerm.e_range)
            FStar_Errors.__proj__Mkissue__item__issue_range in
        let uu___7 =
          let uu___8 =
            let uu___9 = mk_lid "context_of_issue" in
            FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___9
              FStar_Syntax_Embeddings.e_issue
              FStar_TypeChecker_NBETerm.e_issue
              FStar_Syntax_Embeddings.e_string_list
              FStar_TypeChecker_NBETerm.e_string_list
              FStar_Errors.__proj__Mkissue__item__issue_ctx in
          let uu___9 =
            let uu___10 =
              let uu___11 = mk_lid "render_issue" in
              FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___11
                FStar_Syntax_Embeddings.e_issue
                FStar_TypeChecker_NBETerm.e_issue
                FStar_Syntax_Embeddings.e_string
                FStar_TypeChecker_NBETerm.e_string FStar_Errors.format_issue in
            let uu___11 =
              let uu___12 =
                let uu___13 = mk_lid "mk_issue_doc" in
                FStar_TypeChecker_Primops_Base.mk5 Prims.int_zero uu___13
                  FStar_Syntax_Embeddings.e_string
                  FStar_TypeChecker_NBETerm.e_string
                  (FStar_Syntax_Embeddings.e_list
                     FStar_Syntax_Embeddings.e_document)
                  (FStar_TypeChecker_NBETerm.e_list
                     FStar_TypeChecker_NBETerm.e_document)
                  (FStar_Syntax_Embeddings.e_option
                     FStar_Syntax_Embeddings.e_range)
                  (FStar_TypeChecker_NBETerm.e_option
                     FStar_TypeChecker_NBETerm.e_range)
                  (FStar_Syntax_Embeddings.e_option
                     FStar_Syntax_Embeddings.e_int)
                  (FStar_TypeChecker_NBETerm.e_option
                     FStar_TypeChecker_NBETerm.e_int)
                  FStar_Syntax_Embeddings.e_string_list
                  FStar_TypeChecker_NBETerm.e_string_list
                  FStar_Syntax_Embeddings.e_issue
                  FStar_TypeChecker_NBETerm.e_issue
                  (fun level ->
                     fun msg ->
                       fun range ->
                         fun number ->
                           fun context ->
                             let uu___14 =
                               FStar_Errors.issue_level_of_string level in
                             let uu___15 =
                               Obj.magic
                                 (FStar_Class_Monad.fmap
                                    FStar_Class_Monad.monad_option () ()
                                    (fun uu___16 ->
                                       (Obj.magic FStar_BigInt.to_int_fs)
                                         uu___16) (Obj.magic number)) in
                             {
                               FStar_Errors.issue_msg = msg;
                               FStar_Errors.issue_level = uu___14;
                               FStar_Errors.issue_range = range;
                               FStar_Errors.issue_number = uu___15;
                               FStar_Errors.issue_ctx = context
                             }) in
              [uu___12] in
            uu___10 :: uu___11 in
          uu___8 :: uu___9 in
        uu___6 :: uu___7 in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1