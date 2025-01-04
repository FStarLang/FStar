open Prims
let (ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let mk_lid l = FStarC_Parser_Const.p2l ["FStar"; "Issue"; l] in
  let uu___ =
    let uu___1 = mk_lid "message_of_issue" in
    FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___1
      FStarC_Syntax_Embeddings.e_issue FStarC_TypeChecker_NBETerm.e_issue
      (FStarC_Syntax_Embeddings.e_list FStarC_Syntax_Embeddings.e_document)
      (FStarC_TypeChecker_NBETerm.e_list
         FStarC_TypeChecker_NBETerm.e_document)
      FStarC_Errors.__proj__Mkissue__item__issue_msg in
  let uu___1 =
    let uu___2 =
      let uu___3 = mk_lid "level_of_issue" in
      FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___3
        FStarC_Syntax_Embeddings.e_issue FStarC_TypeChecker_NBETerm.e_issue
        FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
        (fun i ->
           FStarC_Errors.string_of_issue_level i.FStarC_Errors.issue_level) in
    let uu___3 =
      let uu___4 =
        let uu___5 = mk_lid "number_of_issue" in
        FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___5
          FStarC_Syntax_Embeddings.e_issue FStarC_TypeChecker_NBETerm.e_issue
          (FStarC_Syntax_Embeddings.e_option FStarC_Syntax_Embeddings.e_int)
          (FStarC_TypeChecker_NBETerm.e_option
             FStarC_TypeChecker_NBETerm.e_int)
          (fun uu___6 ->
             (fun i ->
                Obj.magic
                  (FStarC_Class_Monad.fmap FStarC_Class_Monad.monad_option ()
                     ()
                     (fun uu___6 ->
                        (Obj.magic FStarC_BigInt.of_int_fs) uu___6)
                     (Obj.magic i.FStarC_Errors.issue_number))) uu___6) in
      let uu___5 =
        let uu___6 =
          let uu___7 = mk_lid "range_of_issue" in
          FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___7
            FStarC_Syntax_Embeddings.e_issue
            FStarC_TypeChecker_NBETerm.e_issue
            (FStarC_Syntax_Embeddings.e_option
               FStarC_Syntax_Embeddings.e_range)
            (FStarC_TypeChecker_NBETerm.e_option
               FStarC_TypeChecker_NBETerm.e_range)
            FStarC_Errors.__proj__Mkissue__item__issue_range in
        let uu___7 =
          let uu___8 =
            let uu___9 = mk_lid "context_of_issue" in
            FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___9
              FStarC_Syntax_Embeddings.e_issue
              FStarC_TypeChecker_NBETerm.e_issue
              FStarC_Syntax_Embeddings.e_string_list
              FStarC_TypeChecker_NBETerm.e_string_list
              FStarC_Errors.__proj__Mkissue__item__issue_ctx in
          let uu___9 =
            let uu___10 =
              let uu___11 = mk_lid "render_issue" in
              FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___11
                FStarC_Syntax_Embeddings.e_issue
                FStarC_TypeChecker_NBETerm.e_issue
                FStarC_Syntax_Embeddings.e_string
                FStarC_TypeChecker_NBETerm.e_string
                FStarC_Errors.format_issue in
            let uu___11 =
              let uu___12 =
                let uu___13 = mk_lid "mk_issue_doc" in
                FStarC_TypeChecker_Primops_Base.mk5 Prims.int_zero uu___13
                  FStarC_Syntax_Embeddings.e_string
                  FStarC_TypeChecker_NBETerm.e_string
                  (FStarC_Syntax_Embeddings.e_list
                     FStarC_Syntax_Embeddings.e_document)
                  (FStarC_TypeChecker_NBETerm.e_list
                     FStarC_TypeChecker_NBETerm.e_document)
                  (FStarC_Syntax_Embeddings.e_option
                     FStarC_Syntax_Embeddings.e_range)
                  (FStarC_TypeChecker_NBETerm.e_option
                     FStarC_TypeChecker_NBETerm.e_range)
                  (FStarC_Syntax_Embeddings.e_option
                     FStarC_Syntax_Embeddings.e_int)
                  (FStarC_TypeChecker_NBETerm.e_option
                     FStarC_TypeChecker_NBETerm.e_int)
                  FStarC_Syntax_Embeddings.e_string_list
                  FStarC_TypeChecker_NBETerm.e_string_list
                  FStarC_Syntax_Embeddings.e_issue
                  FStarC_TypeChecker_NBETerm.e_issue
                  (fun level ->
                     fun msg ->
                       fun range ->
                         fun number ->
                           fun context ->
                             let uu___14 =
                               FStarC_Errors.issue_level_of_string level in
                             let uu___15 =
                               Obj.magic
                                 (FStarC_Class_Monad.fmap
                                    FStarC_Class_Monad.monad_option () ()
                                    (fun uu___16 ->
                                       (Obj.magic FStarC_BigInt.to_int_fs)
                                         uu___16) (Obj.magic number)) in
                             {
                               FStarC_Errors.issue_msg = msg;
                               FStarC_Errors.issue_level = uu___14;
                               FStarC_Errors.issue_range = range;
                               FStarC_Errors.issue_number = uu___15;
                               FStarC_Errors.issue_ctx = context
                             }) in
              [uu___12] in
            uu___10 :: uu___11 in
          uu___8 :: uu___9 in
        uu___6 :: uu___7 in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1