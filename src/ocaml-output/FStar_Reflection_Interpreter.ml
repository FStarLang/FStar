open Prims
let unembed :
  'Auu____60987 .
    'Auu____60987 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____60987 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____61011 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____61011 true norm_cb
  
let try_unembed :
  'Auu____61028 .
    'Auu____61028 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____61028 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____61052 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____61052 false norm_cb
  
let embed :
  'Auu____61071 .
    'Auu____61071 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____61071 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea  ->
    fun r  ->
      fun x  ->
        fun norm_cb  ->
          let uu____61098 = FStar_Syntax_Embeddings.embed ea x  in
          uu____61098 r FStar_Pervasives_Native.None norm_cb
  
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
                | (a,uu____61181)::[] ->
                    let uu____61206 = try_unembed ea a n1  in
                    FStar_Util.bind_opt uu____61206
                      (fun a1  ->
                         let uu____61212 =
                           let uu____61213 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           let uu____61214 = f a1  in
                           embed er uu____61213 uu____61214 n1  in
                         FStar_Pervasives_Native.Some uu____61212)
                | uu____61215 -> FStar_Pervasives_Native.None
  
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
                  | (a,uu____61309)::(b,uu____61311)::[] ->
                      let uu____61352 = try_unembed ea a n1  in
                      FStar_Util.bind_opt uu____61352
                        (fun a1  ->
                           let uu____61358 = try_unembed eb b n1  in
                           FStar_Util.bind_opt uu____61358
                             (fun b1  ->
                                let uu____61364 =
                                  let uu____61365 =
                                    FStar_TypeChecker_Cfg.psc_range psc  in
                                  let uu____61366 = f a1 b1  in
                                  embed er uu____61365 uu____61366 n1  in
                                FStar_Pervasives_Native.Some uu____61364))
                  | uu____61367 -> FStar_Pervasives_Native.None
  
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
              | (a,uu____61433)::[] ->
                  let uu____61442 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____61442
                    (fun a1  ->
                       let uu____61448 =
                         let uu____61449 = f a1  in
                         FStar_TypeChecker_NBETerm.embed er cb uu____61449
                          in
                       FStar_Pervasives_Native.Some uu____61448)
              | uu____61450 -> FStar_Pervasives_Native.None
  
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
                | (a,uu____61535)::(b,uu____61537)::[] ->
                    let uu____61550 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a  in
                    FStar_Util.bind_opt uu____61550
                      (fun a1  ->
                         let uu____61556 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____61556
                           (fun b1  ->
                              let uu____61562 =
                                let uu____61563 = f a1 b1  in
                                FStar_TypeChecker_NBETerm.embed er cb
                                  uu____61563
                                 in
                              FStar_Pervasives_Native.Some uu____61562))
                | uu____61564 -> FStar_Pervasives_Native.None
  
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
  let uu____61860 =
    mk1 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
      FStar_Reflection_Basic.inspect_ln FStar_Reflection_NBEEmbeddings.e_term
      FStar_Reflection_NBEEmbeddings.e_term_view
     in
  let uu____61862 =
    let uu____61865 =
      mk1 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term FStar_Reflection_Basic.pack_ln
        FStar_Reflection_NBEEmbeddings.e_term_view
        FStar_Reflection_NBEEmbeddings.e_term
       in
    let uu____61867 =
      let uu____61870 =
        mk1 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
          FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_NBEEmbeddings.e_fv
          FStar_TypeChecker_NBETerm.e_string_list
         in
      let uu____61878 =
        let uu____61881 =
          mk1 "pack_fv" FStar_Reflection_Basic.pack_fv
            FStar_Syntax_Embeddings.e_string_list
            FStar_Reflection_Embeddings.e_fv FStar_Reflection_Basic.pack_fv
            FStar_TypeChecker_NBETerm.e_string_list
            FStar_Reflection_NBEEmbeddings.e_fv
           in
        let uu____61889 =
          let uu____61892 =
            mk1 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
              FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_NBEEmbeddings.e_comp
              FStar_Reflection_NBEEmbeddings.e_comp_view
             in
          let uu____61894 =
            let uu____61897 =
              mk1 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
                FStar_Reflection_Basic.pack_comp
                FStar_Reflection_NBEEmbeddings.e_comp_view
                FStar_Reflection_NBEEmbeddings.e_comp
               in
            let uu____61899 =
              let uu____61902 =
                mk1 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                  FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt_view
                 in
              let uu____61904 =
                let uu____61907 =
                  mk1 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                    FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_NBEEmbeddings.e_sigelt_view
                    FStar_Reflection_NBEEmbeddings.e_sigelt
                   in
                let uu____61909 =
                  let uu____61912 =
                    mk1 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                      FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_NBEEmbeddings.e_bv
                      FStar_Reflection_NBEEmbeddings.e_bv_view
                     in
                  let uu____61914 =
                    let uu____61917 =
                      mk1 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                        FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_NBEEmbeddings.e_bv_view
                        FStar_Reflection_NBEEmbeddings.e_bv
                       in
                    let uu____61919 =
                      let uu____61922 =
                        mk1 "sigelt_attrs"
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_Embeddings.e_sigelt
                          FStar_Reflection_Embeddings.e_attributes
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_NBEEmbeddings.e_sigelt
                          FStar_Reflection_NBEEmbeddings.e_attributes
                         in
                      let uu____61928 =
                        let uu____61931 =
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
                        let uu____61937 =
                          let uu____61940 =
                            mk1 "inspect_binder"
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder_view
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_NBEEmbeddings.e_binder
                              FStar_Reflection_NBEEmbeddings.e_binder_view
                             in
                          let uu____61942 =
                            let uu____61945 =
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
                            let uu____61947 =
                              let uu____61950 =
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
                              let uu____61952 =
                                let uu____61955 =
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
                                let uu____61959 =
                                  let uu____61962 =
                                    let uu____61963 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Reflection_Embeddings.e_fv
                                       in
                                    let uu____61968 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Reflection_NBEEmbeddings.e_fv
                                       in
                                    mk2 "lookup_attr"
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_Embeddings.e_term
                                      FStar_Reflection_Embeddings.e_env
                                      uu____61963
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_NBEEmbeddings.e_term
                                      FStar_Reflection_NBEEmbeddings.e_env
                                      uu____61968
                                     in
                                  let uu____61978 =
                                    let uu____61981 =
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
                                    let uu____61985 =
                                      let uu____61988 =
                                        mk1 "moduleof"
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_Embeddings.e_env
                                          FStar_Syntax_Embeddings.e_string_list
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_NBEEmbeddings.e_env
                                          FStar_TypeChecker_NBETerm.e_string_list
                                         in
                                      let uu____61996 =
                                        let uu____61999 =
                                          mk1 "term_to_string"
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_string
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_NBEEmbeddings.e_term
                                            FStar_TypeChecker_NBETerm.e_string
                                           in
                                        let uu____62003 =
                                          let uu____62006 =
                                            mk1 "binders_of_env"
                                              FStar_Reflection_Basic.binders_of_env
                                              FStar_Reflection_Embeddings.e_env
                                              FStar_Reflection_Embeddings.e_binders
                                              FStar_Reflection_Basic.binders_of_env
                                              FStar_Reflection_NBEEmbeddings.e_env
                                              FStar_Reflection_NBEEmbeddings.e_binders
                                             in
                                          let uu____62008 =
                                            let uu____62011 =
                                              let uu____62012 =
                                                FStar_Syntax_Embeddings.e_option
                                                  FStar_Reflection_Embeddings.e_sigelt
                                                 in
                                              let uu____62017 =
                                                FStar_TypeChecker_NBETerm.e_option
                                                  FStar_Reflection_NBEEmbeddings.e_sigelt
                                                 in
                                              mk2 "lookup_typ"
                                                FStar_Reflection_Basic.lookup_typ
                                                FStar_Reflection_Embeddings.e_env
                                                FStar_Syntax_Embeddings.e_string_list
                                                uu____62012
                                                FStar_Reflection_Basic.lookup_typ
                                                FStar_Reflection_NBEEmbeddings.e_env
                                                FStar_TypeChecker_NBETerm.e_string_list
                                                uu____62017
                                               in
                                            [uu____62011]  in
                                          uu____62006 :: uu____62008  in
                                        uu____61999 :: uu____62003  in
                                      uu____61988 :: uu____61996  in
                                    uu____61981 :: uu____61985  in
                                  uu____61962 :: uu____61978  in
                                uu____61955 :: uu____61959  in
                              uu____61950 :: uu____61952  in
                            uu____61945 :: uu____61947  in
                          uu____61940 :: uu____61942  in
                        uu____61931 :: uu____61937  in
                      uu____61922 :: uu____61928  in
                    uu____61917 :: uu____61919  in
                  uu____61912 :: uu____61914  in
                uu____61907 :: uu____61909  in
              uu____61902 :: uu____61904  in
            uu____61897 :: uu____61899  in
          uu____61892 :: uu____61894  in
        uu____61881 :: uu____61889  in
      uu____61870 :: uu____61878  in
    uu____61865 :: uu____61867  in
  uu____61860 :: uu____61862 