open Prims
let unembed :
  'Auu____65899 .
    'Auu____65899 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____65899 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____65925 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____65925 true norm_cb
  
let try_unembed :
  'Auu____65948 .
    'Auu____65948 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____65948 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____65974 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____65974 false norm_cb
  
let embed :
  'Auu____65999 .
    'Auu____65999 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____65999 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea  ->
    fun r  ->
      fun x  ->
        fun norm_cb  ->
          let uu____66028 = FStar_Syntax_Embeddings.embed ea x  in
          uu____66028 r FStar_Pervasives_Native.None norm_cb
  
let int1 :
  'a 'r .
    FStar_Ident.lid ->
      ('a -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_TypeChecker_Cfg.psc ->
              FStar_Syntax_Embeddings.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun er  ->
          fun psc  ->
            fun n1  ->
              fun args  ->
                match args with
                | (a,uu____66138)::[] ->
                    let uu____66163 = try_unembed ea a n1  in
                    FStar_Util.bind_opt uu____66163
                      (fun a1  ->
                         let uu____66171 =
                           let uu____66172 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           let uu____66173 = f a1  in
                           embed er uu____66172 uu____66173 n1  in
                         FStar_Pervasives_Native.Some uu____66171)
                | uu____66176 -> FStar_Pervasives_Native.None
  
let int2 :
  'a 'b 'r .
    FStar_Ident.lid ->
      ('a -> 'b -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_TypeChecker_Cfg.psc ->
                FStar_Syntax_Embeddings.norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            fun psc  ->
              fun n1  ->
                fun args  ->
                  match args with
                  | (a,uu____66272)::(b,uu____66274)::[] ->
                      let uu____66315 = try_unembed ea a n1  in
                      FStar_Util.bind_opt uu____66315
                        (fun a1  ->
                           let uu____66323 = try_unembed eb b n1  in
                           FStar_Util.bind_opt uu____66323
                             (fun b1  ->
                                let uu____66331 =
                                  let uu____66332 =
                                    FStar_TypeChecker_Cfg.psc_range psc  in
                                  let uu____66333 = f a1 b1  in
                                  embed er uu____66332 uu____66333 n1  in
                                FStar_Pervasives_Native.Some uu____66331))
                  | uu____66336 -> FStar_Pervasives_Native.None
  
let nbe_int1 :
  'a 'r .
    FStar_Ident.lid ->
      ('a -> 'r) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.nbe_cbs ->
              FStar_TypeChecker_NBETerm.args ->
                FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun er  ->
          fun cb  ->
            fun args  ->
              match args with
              | (a,uu____66402)::[] ->
                  let uu____66411 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____66411
                    (fun a1  ->
                       let uu____66417 =
                         let uu____66418 = f a1  in
                         FStar_TypeChecker_NBETerm.embed er cb uu____66418
                          in
                       FStar_Pervasives_Native.Some uu____66417)
              | uu____66419 -> FStar_Pervasives_Native.None
  
let nbe_int2 :
  'a 'b 'r .
    FStar_Ident.lid ->
      ('a -> 'b -> 'r) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'b FStar_TypeChecker_NBETerm.embedding ->
            'r FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.nbe_cbs ->
                FStar_TypeChecker_NBETerm.args ->
                  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            fun cb  ->
              fun args  ->
                match args with
                | (a,uu____66504)::(b,uu____66506)::[] ->
                    let uu____66519 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a  in
                    FStar_Util.bind_opt uu____66519
                      (fun a1  ->
                         let uu____66525 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____66525
                           (fun b1  ->
                              let uu____66531 =
                                let uu____66532 = f a1 b1  in
                                FStar_TypeChecker_NBETerm.embed er cb
                                  uu____66532
                                 in
                              FStar_Pervasives_Native.Some uu____66531))
                | uu____66533 -> FStar_Pervasives_Native.None
  
let (mklid : Prims.string -> FStar_Ident.lid) =
  fun nm  -> FStar_Reflection_Data.fstar_refl_basic_lid nm 
let (mk :
  FStar_Ident.lid ->
    Prims.int ->
      (FStar_TypeChecker_Cfg.psc ->
         FStar_Syntax_Embeddings.norm_cb ->
           FStar_Syntax_Syntax.args ->
             FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_NBETerm.nbe_cbs ->
           FStar_TypeChecker_NBETerm.args ->
             FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
          -> FStar_TypeChecker_Cfg.primitive_step)
  =
  fun l  ->
    fun arity  ->
      fun fn  ->
        fun nbe_fn  ->
          {
            FStar_TypeChecker_Cfg.name = l;
            FStar_TypeChecker_Cfg.arity = arity;
            FStar_TypeChecker_Cfg.univ_arity = (Prims.parse_int "0");
            FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.None;
            FStar_TypeChecker_Cfg.strong_reduction_ok = true;
            FStar_TypeChecker_Cfg.requires_binder_substitution = false;
            FStar_TypeChecker_Cfg.interpretation = fn;
            FStar_TypeChecker_Cfg.interpretation_nbe = nbe_fn
          }
  
let mk1 :
  'a 'na 'nr 'r .
    Prims.string ->
      ('a -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            ('na -> 'nr) ->
              'na FStar_TypeChecker_NBETerm.embedding ->
                'nr FStar_TypeChecker_NBETerm.embedding ->
                  FStar_TypeChecker_Cfg.primitive_step
  =
  fun nm  ->
    fun f  ->
      fun ea  ->
        fun er  ->
          fun nf  ->
            fun ena  ->
              fun enr  ->
                let l = mklid nm  in
                mk l (Prims.parse_int "1") (int1 l f ea er)
                  (nbe_int1 l nf ena enr)
  
let mk2 :
  'a 'b 'na 'nb 'nr 'r .
    Prims.string ->
      ('a -> 'b -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              ('na -> 'nb -> 'nr) ->
                'na FStar_TypeChecker_NBETerm.embedding ->
                  'nb FStar_TypeChecker_NBETerm.embedding ->
                    'nr FStar_TypeChecker_NBETerm.embedding ->
                      FStar_TypeChecker_Cfg.primitive_step
  =
  fun nm  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            fun nf  ->
              fun ena  ->
                fun enb  ->
                  fun enr  ->
                    let l = mklid nm  in
                    mk l (Prims.parse_int "2") (int2 l f ea eb er)
                      (nbe_int2 l nf ena enb enr)
  
let (reflection_primops : FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  let uu____66831 =
    mk1 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
      FStar_Reflection_Basic.inspect_ln FStar_Reflection_NBEEmbeddings.e_term
      FStar_Reflection_NBEEmbeddings.e_term_view
     in
  let uu____66833 =
    let uu____66836 =
      mk1 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term FStar_Reflection_Basic.pack_ln
        FStar_Reflection_NBEEmbeddings.e_term_view
        FStar_Reflection_NBEEmbeddings.e_term
       in
    let uu____66838 =
      let uu____66841 =
        mk1 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
          FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_NBEEmbeddings.e_fv
          FStar_TypeChecker_NBETerm.e_string_list
         in
      let uu____66849 =
        let uu____66852 =
          mk1 "pack_fv" FStar_Reflection_Basic.pack_fv
            FStar_Syntax_Embeddings.e_string_list
            FStar_Reflection_Embeddings.e_fv FStar_Reflection_Basic.pack_fv
            FStar_TypeChecker_NBETerm.e_string_list
            FStar_Reflection_NBEEmbeddings.e_fv
           in
        let uu____66860 =
          let uu____66863 =
            mk1 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
              FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_NBEEmbeddings.e_comp
              FStar_Reflection_NBEEmbeddings.e_comp_view
             in
          let uu____66865 =
            let uu____66868 =
              mk1 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
                FStar_Reflection_Basic.pack_comp
                FStar_Reflection_NBEEmbeddings.e_comp_view
                FStar_Reflection_NBEEmbeddings.e_comp
               in
            let uu____66870 =
              let uu____66873 =
                mk1 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                  FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt_view
                 in
              let uu____66875 =
                let uu____66878 =
                  mk1 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                    FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_NBEEmbeddings.e_sigelt_view
                    FStar_Reflection_NBEEmbeddings.e_sigelt
                   in
                let uu____66880 =
                  let uu____66883 =
                    mk1 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                      FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_NBEEmbeddings.e_bv
                      FStar_Reflection_NBEEmbeddings.e_bv_view
                     in
                  let uu____66885 =
                    let uu____66888 =
                      mk1 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                        FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_NBEEmbeddings.e_bv_view
                        FStar_Reflection_NBEEmbeddings.e_bv
                       in
                    let uu____66890 =
                      let uu____66893 =
                        mk1 "sigelt_attrs"
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_Embeddings.e_sigelt
                          FStar_Reflection_Embeddings.e_attributes
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_NBEEmbeddings.e_sigelt
                          FStar_Reflection_NBEEmbeddings.e_attributes
                         in
                      let uu____66899 =
                        let uu____66902 =
                          mk2 "set_sigelt_attrs"
                            FStar_Reflection_Basic.set_sigelt_attrs
                            FStar_Reflection_Embeddings.e_attributes
                            FStar_Reflection_Embeddings.e_sigelt
                            FStar_Reflection_Embeddings.e_sigelt
                            FStar_Reflection_Basic.set_sigelt_attrs
                            FStar_Reflection_NBEEmbeddings.e_attributes
                            FStar_Reflection_NBEEmbeddings.e_sigelt
                            FStar_Reflection_NBEEmbeddings.e_sigelt
                           in
                        let uu____66908 =
                          let uu____66911 =
                            mk1 "inspect_binder"
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder_view
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_NBEEmbeddings.e_binder
                              FStar_Reflection_NBEEmbeddings.e_binder_view
                             in
                          let uu____66913 =
                            let uu____66916 =
                              mk2 "pack_binder"
                                FStar_Reflection_Basic.pack_binder
                                FStar_Reflection_Embeddings.e_bv
                                FStar_Reflection_Embeddings.e_aqualv
                                FStar_Reflection_Embeddings.e_binder
                                FStar_Reflection_Basic.pack_binder
                                FStar_Reflection_NBEEmbeddings.e_bv
                                FStar_Reflection_NBEEmbeddings.e_aqualv
                                FStar_Reflection_NBEEmbeddings.e_binder
                               in
                            let uu____66918 =
                              let uu____66921 =
                                mk2 "compare_bv"
                                  FStar_Reflection_Basic.compare_bv
                                  FStar_Reflection_Embeddings.e_bv
                                  FStar_Reflection_Embeddings.e_bv
                                  FStar_Reflection_Embeddings.e_order
                                  FStar_Reflection_Basic.compare_bv
                                  FStar_Reflection_NBEEmbeddings.e_bv
                                  FStar_Reflection_NBEEmbeddings.e_bv
                                  FStar_Reflection_NBEEmbeddings.e_order
                                 in
                              let uu____66923 =
                                let uu____66926 =
                                  mk2 "is_free"
                                    FStar_Reflection_Basic.is_free
                                    FStar_Reflection_Embeddings.e_bv
                                    FStar_Reflection_Embeddings.e_term
                                    FStar_Syntax_Embeddings.e_bool
                                    FStar_Reflection_Basic.is_free
                                    FStar_Reflection_NBEEmbeddings.e_bv
                                    FStar_Reflection_NBEEmbeddings.e_term
                                    FStar_TypeChecker_NBETerm.e_bool
                                   in
                                let uu____66930 =
                                  let uu____66933 =
                                    let uu____66934 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Reflection_Embeddings.e_fv
                                       in
                                    let uu____66939 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Reflection_NBEEmbeddings.e_fv
                                       in
                                    mk2 "lookup_attr"
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_Embeddings.e_term
                                      FStar_Reflection_Embeddings.e_env
                                      uu____66934
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_NBEEmbeddings.e_term
                                      FStar_Reflection_NBEEmbeddings.e_env
                                      uu____66939
                                     in
                                  let uu____66949 =
                                    let uu____66952 =
                                      mk2 "term_eq"
                                        FStar_Reflection_Basic.term_eq
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Syntax_Embeddings.e_bool
                                        FStar_Reflection_Basic.term_eq
                                        FStar_Reflection_NBEEmbeddings.e_term
                                        FStar_Reflection_NBEEmbeddings.e_term
                                        FStar_TypeChecker_NBETerm.e_bool
                                       in
                                    let uu____66956 =
                                      let uu____66959 =
                                        mk1 "moduleof"
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_Embeddings.e_env
                                          FStar_Syntax_Embeddings.e_string_list
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_NBEEmbeddings.e_env
                                          FStar_TypeChecker_NBETerm.e_string_list
                                         in
                                      let uu____66967 =
                                        let uu____66970 =
                                          mk1 "term_to_string"
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_string
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_NBEEmbeddings.e_term
                                            FStar_TypeChecker_NBETerm.e_string
                                           in
                                        let uu____66974 =
                                          let uu____66977 =
                                            mk1 "binders_of_env"
                                              FStar_Reflection_Basic.binders_of_env
                                              FStar_Reflection_Embeddings.e_env
                                              FStar_Reflection_Embeddings.e_binders
                                              FStar_Reflection_Basic.binders_of_env
                                              FStar_Reflection_NBEEmbeddings.e_env
                                              FStar_Reflection_NBEEmbeddings.e_binders
                                             in
                                          let uu____66979 =
                                            let uu____66982 =
                                              let uu____66983 =
                                                FStar_Syntax_Embeddings.e_option
                                                  FStar_Reflection_Embeddings.e_sigelt
                                                 in
                                              let uu____66988 =
                                                FStar_TypeChecker_NBETerm.e_option
                                                  FStar_Reflection_NBEEmbeddings.e_sigelt
                                                 in
                                              mk2 "lookup_typ"
                                                FStar_Reflection_Basic.lookup_typ
                                                FStar_Reflection_Embeddings.e_env
                                                FStar_Syntax_Embeddings.e_string_list
                                                uu____66983
                                                FStar_Reflection_Basic.lookup_typ
                                                FStar_Reflection_NBEEmbeddings.e_env
                                                FStar_TypeChecker_NBETerm.e_string_list
                                                uu____66988
                                               in
                                            [uu____66982]  in
                                          uu____66977 :: uu____66979  in
                                        uu____66970 :: uu____66974  in
                                      uu____66959 :: uu____66967  in
                                    uu____66952 :: uu____66956  in
                                  uu____66933 :: uu____66949  in
                                uu____66926 :: uu____66930  in
                              uu____66921 :: uu____66923  in
                            uu____66916 :: uu____66918  in
                          uu____66911 :: uu____66913  in
                        uu____66902 :: uu____66908  in
                      uu____66893 :: uu____66899  in
                    uu____66888 :: uu____66890  in
                  uu____66883 :: uu____66885  in
                uu____66878 :: uu____66880  in
              uu____66873 :: uu____66875  in
            uu____66868 :: uu____66870  in
          uu____66863 :: uu____66865  in
        uu____66852 :: uu____66860  in
      uu____66841 :: uu____66849  in
    uu____66836 :: uu____66838  in
  uu____66831 :: uu____66833 