open Prims
let (bogus_cbs : FStarC_TypeChecker_NBETerm.nbe_cbs) =
  {
    FStarC_TypeChecker_NBETerm.iapp = (fun h -> fun _args -> h);
    FStarC_TypeChecker_NBETerm.translate =
      (fun uu___ -> failwith "bogus_cbs translate")
  }
let (ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  FStarC_Compiler_List.map
    (fun p ->
       let uu___ =
         FStarC_TypeChecker_Primops_Base.as_primitive_step_nbecbs true p in
       {
         FStarC_TypeChecker_Primops_Base.name =
           (uu___.FStarC_TypeChecker_Primops_Base.name);
         FStarC_TypeChecker_Primops_Base.arity =
           (uu___.FStarC_TypeChecker_Primops_Base.arity);
         FStarC_TypeChecker_Primops_Base.univ_arity =
           (uu___.FStarC_TypeChecker_Primops_Base.univ_arity);
         FStarC_TypeChecker_Primops_Base.auto_reflect =
           (uu___.FStarC_TypeChecker_Primops_Base.auto_reflect);
         FStarC_TypeChecker_Primops_Base.strong_reduction_ok =
           (uu___.FStarC_TypeChecker_Primops_Base.strong_reduction_ok);
         FStarC_TypeChecker_Primops_Base.requires_binder_substitution =
           (uu___.FStarC_TypeChecker_Primops_Base.requires_binder_substitution);
         FStarC_TypeChecker_Primops_Base.renorm_after = true;
         FStarC_TypeChecker_Primops_Base.interpretation =
           (uu___.FStarC_TypeChecker_Primops_Base.interpretation);
         FStarC_TypeChecker_Primops_Base.interpretation_nbe =
           (uu___.FStarC_TypeChecker_Primops_Base.interpretation_nbe)
       })
    [(FStarC_Parser_Const.map_seal_lid, (Prims.of_int (4)),
       (Prims.of_int (2)),
       ((fun psc ->
           fun univs ->
             fun cbs ->
               fun args ->
                 match args with
                 | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                     let try_unembed e x =
                       FStarC_Syntax_Embeddings_Base.try_unembed e x
                         FStarC_Syntax_Embeddings_Base.id_norm_cb in
                     let uu___4 =
                       let uu___5 =
                         try_unembed FStarC_Syntax_Embeddings.e_any ta in
                       let uu___6 =
                         try_unembed FStarC_Syntax_Embeddings.e_any tb in
                       let uu___7 =
                         try_unembed
                           (FStarC_Syntax_Embeddings.e_sealed
                              FStarC_Syntax_Embeddings.e_any) s in
                       let uu___8 =
                         try_unembed FStarC_Syntax_Embeddings.e_any f in
                       (uu___5, uu___6, uu___7, uu___8) in
                     (match uu___4 with
                      | (FStar_Pervasives_Native.Some ta1,
                         FStar_Pervasives_Native.Some tb1,
                         FStar_Pervasives_Native.Some s1,
                         FStar_Pervasives_Native.Some f1) ->
                          let r =
                            let uu___5 =
                              let uu___6 =
                                FStarC_Syntax_Syntax.as_arg
                                  (FStarC_Compiler_Sealed.unseal s1) in
                              [uu___6] in
                            FStarC_Syntax_Util.mk_app f1 uu___5 in
                          let emb =
                            FStarC_Syntax_Embeddings_Base.set_type ta1
                              FStarC_Syntax_Embeddings.e_any in
                          let uu___5 =
                            FStarC_TypeChecker_Primops_Base.embed_simple
                              (FStarC_Syntax_Embeddings.e_sealed emb)
                              psc.FStarC_TypeChecker_Primops_Base.psc_range
                              (FStarC_Compiler_Sealed.seal r) in
                          FStar_Pervasives_Native.Some uu___5
                      | uu___5 -> FStar_Pervasives_Native.None)
                 | uu___ -> FStar_Pervasives_Native.None)),
       ((fun cb ->
           fun univs ->
             fun args ->
               match args with
               | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                   let try_unembed e x =
                     FStarC_TypeChecker_NBETerm.unembed e bogus_cbs x in
                   let uu___4 =
                     let uu___5 =
                       try_unembed FStarC_TypeChecker_NBETerm.e_any ta in
                     let uu___6 =
                       try_unembed FStarC_TypeChecker_NBETerm.e_any tb in
                     let uu___7 =
                       try_unembed
                         (FStarC_TypeChecker_NBETerm.e_sealed
                            FStarC_TypeChecker_NBETerm.e_any) s in
                     let uu___8 =
                       try_unembed FStarC_TypeChecker_NBETerm.e_any f in
                     (uu___5, uu___6, uu___7, uu___8) in
                   (match uu___4 with
                    | (FStar_Pervasives_Native.Some ta1,
                       FStar_Pervasives_Native.Some tb1,
                       FStar_Pervasives_Native.Some s1,
                       FStar_Pervasives_Native.Some f1) ->
                        let r =
                          let uu___5 =
                            let uu___6 =
                              FStarC_TypeChecker_NBETerm.as_arg
                                (FStarC_Compiler_Sealed.unseal s1) in
                            [uu___6] in
                          cb.FStarC_TypeChecker_NBETerm.iapp f1 uu___5 in
                        let emb =
                          FStarC_TypeChecker_NBETerm.set_type ta1
                            FStarC_TypeChecker_NBETerm.e_any in
                        let uu___5 =
                          FStarC_TypeChecker_NBETerm.embed
                            (FStarC_TypeChecker_NBETerm.e_sealed emb) cb
                            (FStarC_Compiler_Sealed.seal r) in
                        FStar_Pervasives_Native.Some uu___5
                    | uu___5 -> FStar_Pervasives_Native.None)
               | uu___ -> FStar_Pervasives_Native.None)));
    (FStarC_Parser_Const.bind_seal_lid, (Prims.of_int (4)),
      (Prims.of_int (2)),
      ((fun psc ->
          fun univs ->
            fun cbs ->
              fun args ->
                match args with
                | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                    let try_unembed e x =
                      FStarC_Syntax_Embeddings_Base.try_unembed e x
                        FStarC_Syntax_Embeddings_Base.id_norm_cb in
                    let uu___4 =
                      let uu___5 =
                        try_unembed FStarC_Syntax_Embeddings.e_any ta in
                      let uu___6 =
                        try_unembed FStarC_Syntax_Embeddings.e_any tb in
                      let uu___7 =
                        try_unembed
                          (FStarC_Syntax_Embeddings.e_sealed
                             FStarC_Syntax_Embeddings.e_any) s in
                      let uu___8 =
                        try_unembed FStarC_Syntax_Embeddings.e_any f in
                      (uu___5, uu___6, uu___7, uu___8) in
                    (match uu___4 with
                     | (FStar_Pervasives_Native.Some ta1,
                        FStar_Pervasives_Native.Some tb1,
                        FStar_Pervasives_Native.Some s1,
                        FStar_Pervasives_Native.Some f1) ->
                         let r =
                           let uu___5 =
                             let uu___6 =
                               FStarC_Syntax_Syntax.as_arg
                                 (FStarC_Compiler_Sealed.unseal s1) in
                             [uu___6] in
                           FStarC_Syntax_Util.mk_app f1 uu___5 in
                         let uu___5 =
                           FStarC_TypeChecker_Primops_Base.embed_simple
                             FStarC_Syntax_Embeddings.e_any
                             psc.FStarC_TypeChecker_Primops_Base.psc_range r in
                         FStar_Pervasives_Native.Some uu___5
                     | uu___5 -> FStar_Pervasives_Native.None)
                | uu___ -> FStar_Pervasives_Native.None)),
      ((fun cb ->
          fun univs ->
            fun args ->
              match args with
              | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                  let try_unembed e x =
                    FStarC_TypeChecker_NBETerm.unembed e bogus_cbs x in
                  let uu___4 =
                    let uu___5 =
                      try_unembed FStarC_TypeChecker_NBETerm.e_any ta in
                    let uu___6 =
                      try_unembed FStarC_TypeChecker_NBETerm.e_any tb in
                    let uu___7 =
                      try_unembed
                        (FStarC_TypeChecker_NBETerm.e_sealed
                           FStarC_TypeChecker_NBETerm.e_any) s in
                    let uu___8 =
                      try_unembed FStarC_TypeChecker_NBETerm.e_any f in
                    (uu___5, uu___6, uu___7, uu___8) in
                  (match uu___4 with
                   | (FStar_Pervasives_Native.Some ta1,
                      FStar_Pervasives_Native.Some tb1,
                      FStar_Pervasives_Native.Some s1,
                      FStar_Pervasives_Native.Some f1) ->
                       let r =
                         let uu___5 =
                           let uu___6 =
                             FStarC_TypeChecker_NBETerm.as_arg
                               (FStarC_Compiler_Sealed.unseal s1) in
                           [uu___6] in
                         cb.FStarC_TypeChecker_NBETerm.iapp f1 uu___5 in
                       let emb =
                         FStarC_TypeChecker_NBETerm.set_type ta1
                           FStarC_TypeChecker_NBETerm.e_any in
                       let uu___5 = FStarC_TypeChecker_NBETerm.embed emb cb r in
                       FStar_Pervasives_Native.Some uu___5
                   | uu___5 -> FStar_Pervasives_Native.None)
              | uu___ -> FStar_Pervasives_Native.None)))]