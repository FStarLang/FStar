open Prims
let (bogus_cbs : FStar_TypeChecker_NBETerm.nbe_cbs) =
  {
    FStar_TypeChecker_NBETerm.iapp = (fun h -> fun _args -> h);
    FStar_TypeChecker_NBETerm.translate =
      (fun uu___ -> FStar_Compiler_Effect.failwith "bogus_cbs translate")
  }
let (ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  FStar_Compiler_List.map
    (fun p ->
       let uu___ =
         FStar_TypeChecker_Primops_Base.as_primitive_step_nbecbs true p in
       {
         FStar_TypeChecker_Primops_Base.name =
           (uu___.FStar_TypeChecker_Primops_Base.name);
         FStar_TypeChecker_Primops_Base.arity =
           (uu___.FStar_TypeChecker_Primops_Base.arity);
         FStar_TypeChecker_Primops_Base.univ_arity =
           (uu___.FStar_TypeChecker_Primops_Base.univ_arity);
         FStar_TypeChecker_Primops_Base.auto_reflect =
           (uu___.FStar_TypeChecker_Primops_Base.auto_reflect);
         FStar_TypeChecker_Primops_Base.strong_reduction_ok =
           (uu___.FStar_TypeChecker_Primops_Base.strong_reduction_ok);
         FStar_TypeChecker_Primops_Base.requires_binder_substitution =
           (uu___.FStar_TypeChecker_Primops_Base.requires_binder_substitution);
         FStar_TypeChecker_Primops_Base.renorm_after = true;
         FStar_TypeChecker_Primops_Base.interpretation =
           (uu___.FStar_TypeChecker_Primops_Base.interpretation);
         FStar_TypeChecker_Primops_Base.interpretation_nbe =
           (uu___.FStar_TypeChecker_Primops_Base.interpretation_nbe)
       })
    [(FStar_Parser_Const.map_seal_lid, (Prims.of_int (4)),
       (Prims.of_int (2)),
       ((fun psc ->
           fun univs ->
             fun cbs ->
               fun args ->
                 match args with
                 | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                     let try_unembed e x =
                       FStar_Syntax_Embeddings_Base.try_unembed e x
                         FStar_Syntax_Embeddings_Base.id_norm_cb in
                     let uu___4 =
                       let uu___5 =
                         try_unembed FStar_Syntax_Embeddings.e_any ta in
                       let uu___6 =
                         try_unembed FStar_Syntax_Embeddings.e_any tb in
                       let uu___7 =
                         try_unembed
                           (FStar_Syntax_Embeddings.e_sealed
                              FStar_Syntax_Embeddings.e_any) s in
                       let uu___8 =
                         try_unembed FStar_Syntax_Embeddings.e_any f in
                       (uu___5, uu___6, uu___7, uu___8) in
                     (match uu___4 with
                      | (FStar_Pervasives_Native.Some ta1,
                         FStar_Pervasives_Native.Some tb1,
                         FStar_Pervasives_Native.Some s1,
                         FStar_Pervasives_Native.Some f1) ->
                          let r =
                            let uu___5 =
                              let uu___6 =
                                FStar_Syntax_Syntax.as_arg
                                  (FStar_Compiler_Sealed.unseal s1) in
                              [uu___6] in
                            FStar_Syntax_Util.mk_app f1 uu___5 in
                          let emb =
                            FStar_Syntax_Embeddings_Base.set_type ta1
                              FStar_Syntax_Embeddings.e_any in
                          let uu___5 =
                            FStar_TypeChecker_Primops_Base.embed_simple
                              (FStar_Syntax_Embeddings.e_sealed emb)
                              psc.FStar_TypeChecker_Primops_Base.psc_range
                              (FStar_Compiler_Sealed.seal r) in
                          FStar_Pervasives_Native.Some uu___5
                      | uu___5 -> FStar_Pervasives_Native.None)
                 | uu___ -> FStar_Pervasives_Native.None)),
       ((fun cb ->
           fun univs ->
             fun args ->
               match args with
               | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                   let try_unembed e x =
                     FStar_TypeChecker_NBETerm.unembed e bogus_cbs x in
                   let uu___4 =
                     let uu___5 =
                       try_unembed FStar_TypeChecker_NBETerm.e_any ta in
                     let uu___6 =
                       try_unembed FStar_TypeChecker_NBETerm.e_any tb in
                     let uu___7 =
                       try_unembed
                         (FStar_TypeChecker_NBETerm.e_sealed
                            FStar_TypeChecker_NBETerm.e_any) s in
                     let uu___8 =
                       try_unembed FStar_TypeChecker_NBETerm.e_any f in
                     (uu___5, uu___6, uu___7, uu___8) in
                   (match uu___4 with
                    | (FStar_Pervasives_Native.Some ta1,
                       FStar_Pervasives_Native.Some tb1,
                       FStar_Pervasives_Native.Some s1,
                       FStar_Pervasives_Native.Some f1) ->
                        let r =
                          let uu___5 =
                            let uu___6 =
                              FStar_TypeChecker_NBETerm.as_arg
                                (FStar_Compiler_Sealed.unseal s1) in
                            [uu___6] in
                          cb.FStar_TypeChecker_NBETerm.iapp f1 uu___5 in
                        let emb =
                          FStar_TypeChecker_NBETerm.set_type ta1
                            FStar_TypeChecker_NBETerm.e_any in
                        let uu___5 =
                          FStar_TypeChecker_NBETerm.embed
                            (FStar_TypeChecker_NBETerm.e_sealed emb) cb
                            (FStar_Compiler_Sealed.seal r) in
                        FStar_Pervasives_Native.Some uu___5
                    | uu___5 -> FStar_Pervasives_Native.None)
               | uu___ -> FStar_Pervasives_Native.None)));
    (FStar_Parser_Const.bind_seal_lid, (Prims.of_int (4)),
      (Prims.of_int (2)),
      ((fun psc ->
          fun univs ->
            fun cbs ->
              fun args ->
                match args with
                | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                    let try_unembed e x =
                      FStar_Syntax_Embeddings_Base.try_unembed e x
                        FStar_Syntax_Embeddings_Base.id_norm_cb in
                    let uu___4 =
                      let uu___5 =
                        try_unembed FStar_Syntax_Embeddings.e_any ta in
                      let uu___6 =
                        try_unembed FStar_Syntax_Embeddings.e_any tb in
                      let uu___7 =
                        try_unembed
                          (FStar_Syntax_Embeddings.e_sealed
                             FStar_Syntax_Embeddings.e_any) s in
                      let uu___8 =
                        try_unembed FStar_Syntax_Embeddings.e_any f in
                      (uu___5, uu___6, uu___7, uu___8) in
                    (match uu___4 with
                     | (FStar_Pervasives_Native.Some ta1,
                        FStar_Pervasives_Native.Some tb1,
                        FStar_Pervasives_Native.Some s1,
                        FStar_Pervasives_Native.Some f1) ->
                         let r =
                           let uu___5 =
                             let uu___6 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Compiler_Sealed.unseal s1) in
                             [uu___6] in
                           FStar_Syntax_Util.mk_app f1 uu___5 in
                         let uu___5 =
                           FStar_TypeChecker_Primops_Base.embed_simple
                             FStar_Syntax_Embeddings.e_any
                             psc.FStar_TypeChecker_Primops_Base.psc_range r in
                         FStar_Pervasives_Native.Some uu___5
                     | uu___5 -> FStar_Pervasives_Native.None)
                | uu___ -> FStar_Pervasives_Native.None)),
      ((fun cb ->
          fun univs ->
            fun args ->
              match args with
              | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                  let try_unembed e x =
                    FStar_TypeChecker_NBETerm.unembed e bogus_cbs x in
                  let uu___4 =
                    let uu___5 =
                      try_unembed FStar_TypeChecker_NBETerm.e_any ta in
                    let uu___6 =
                      try_unembed FStar_TypeChecker_NBETerm.e_any tb in
                    let uu___7 =
                      try_unembed
                        (FStar_TypeChecker_NBETerm.e_sealed
                           FStar_TypeChecker_NBETerm.e_any) s in
                    let uu___8 =
                      try_unembed FStar_TypeChecker_NBETerm.e_any f in
                    (uu___5, uu___6, uu___7, uu___8) in
                  (match uu___4 with
                   | (FStar_Pervasives_Native.Some ta1,
                      FStar_Pervasives_Native.Some tb1,
                      FStar_Pervasives_Native.Some s1,
                      FStar_Pervasives_Native.Some f1) ->
                       let r =
                         let uu___5 =
                           let uu___6 =
                             FStar_TypeChecker_NBETerm.as_arg
                               (FStar_Compiler_Sealed.unseal s1) in
                           [uu___6] in
                         cb.FStar_TypeChecker_NBETerm.iapp f1 uu___5 in
                       let emb =
                         FStar_TypeChecker_NBETerm.set_type ta1
                           FStar_TypeChecker_NBETerm.e_any in
                       let uu___5 = FStar_TypeChecker_NBETerm.embed emb cb r in
                       FStar_Pervasives_Native.Some uu___5
                   | uu___5 -> FStar_Pervasives_Native.None)
              | uu___ -> FStar_Pervasives_Native.None)))]