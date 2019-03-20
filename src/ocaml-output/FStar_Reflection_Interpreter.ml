open Prims
let unembed :
  'Auu____61007 .
    'Auu____61007 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____61007 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____61031 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____61031 true norm_cb
  
let try_unembed :
  'Auu____61048 .
    'Auu____61048 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____61048 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____61072 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____61072 false norm_cb
  
let embed :
  'Auu____61091 .
    'Auu____61091 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____61091 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea  ->
    fun r  ->
      fun x  ->
        fun norm_cb  ->
          let uu____61118 = FStar_Syntax_Embeddings.embed ea x  in
          uu____61118 r FStar_Pervasives_Native.None norm_cb
  
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
                | (a,uu____61201)::[] ->
                    let uu____61226 = try_unembed ea a n1  in
                    FStar_Util.bind_opt uu____61226
                      (fun a1  ->
                         let uu____61232 =
                           let uu____61233 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           let uu____61234 = f a1  in
                           embed er uu____61233 uu____61234 n1  in
                         FStar_Pervasives_Native.Some uu____61232)
                | uu____61235 -> FStar_Pervasives_Native.None
  
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
                  | (a,uu____61329)::(b,uu____61331)::[] ->
                      let uu____61372 = try_unembed ea a n1  in
                      FStar_Util.bind_opt uu____61372
                        (fun a1  ->
                           let uu____61378 = try_unembed eb b n1  in
                           FStar_Util.bind_opt uu____61378
                             (fun b1  ->
                                let uu____61384 =
                                  let uu____61385 =
                                    FStar_TypeChecker_Cfg.psc_range psc  in
                                  let uu____61386 = f a1 b1  in
                                  embed er uu____61385 uu____61386 n1  in
                                FStar_Pervasives_Native.Some uu____61384))
                  | uu____61387 -> FStar_Pervasives_Native.None
  
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
              | (a,uu____61453)::[] ->
                  let uu____61462 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____61462
                    (fun a1  ->
                       let uu____61468 =
                         let uu____61469 = f a1  in
                         FStar_TypeChecker_NBETerm.embed er cb uu____61469
                          in
                       FStar_Pervasives_Native.Some uu____61468)
              | uu____61470 -> FStar_Pervasives_Native.None
  
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
                | (a,uu____61555)::(b,uu____61557)::[] ->
                    let uu____61570 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a  in
                    FStar_Util.bind_opt uu____61570
                      (fun a1  ->
                         let uu____61576 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____61576
                           (fun b1  ->
                              let uu____61582 =
                                let uu____61583 = f a1 b1  in
                                FStar_TypeChecker_NBETerm.embed er cb
                                  uu____61583
                                 in
                              FStar_Pervasives_Native.Some uu____61582))
                | uu____61584 -> FStar_Pervasives_Native.None
  
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
  let uu____61880 =
    mk1 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
      FStar_Reflection_Basic.inspect_ln FStar_Reflection_NBEEmbeddings.e_term
      FStar_Reflection_NBEEmbeddings.e_term_view
     in
  let uu____61882 =
    let uu____61885 =
      mk1 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term FStar_Reflection_Basic.pack_ln
        FStar_Reflection_NBEEmbeddings.e_term_view
        FStar_Reflection_NBEEmbeddings.e_term
       in
    let uu____61887 =
      let uu____61890 =
        mk1 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
          FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_NBEEmbeddings.e_fv
          FStar_TypeChecker_NBETerm.e_string_list
         in
      let uu____61898 =
        let uu____61901 =
          mk1 "pack_fv" FStar_Reflection_Basic.pack_fv
            FStar_Syntax_Embeddings.e_string_list
            FStar_Reflection_Embeddings.e_fv FStar_Reflection_Basic.pack_fv
            FStar_TypeChecker_NBETerm.e_string_list
            FStar_Reflection_NBEEmbeddings.e_fv
           in
        let uu____61909 =
          let uu____61912 =
            mk1 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
              FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_NBEEmbeddings.e_comp
              FStar_Reflection_NBEEmbeddings.e_comp_view
             in
          let uu____61914 =
            let uu____61917 =
              mk1 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
                FStar_Reflection_Basic.pack_comp
                FStar_Reflection_NBEEmbeddings.e_comp_view
                FStar_Reflection_NBEEmbeddings.e_comp
               in
            let uu____61919 =
              let uu____61922 =
                mk1 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                  FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt_view
                 in
              let uu____61924 =
                let uu____61927 =
                  mk1 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                    FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_NBEEmbeddings.e_sigelt_view
                    FStar_Reflection_NBEEmbeddings.e_sigelt
                   in
                let uu____61929 =
                  let uu____61932 =
                    mk1 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                      FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_NBEEmbeddings.e_bv
                      FStar_Reflection_NBEEmbeddings.e_bv_view
                     in
                  let uu____61934 =
                    let uu____61937 =
                      mk1 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                        FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_NBEEmbeddings.e_bv_view
                        FStar_Reflection_NBEEmbeddings.e_bv
                       in
                    let uu____61939 =
                      let uu____61942 =
                        mk1 "sigelt_attrs"
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_Embeddings.e_sigelt
                          FStar_Reflection_Embeddings.e_attributes
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_NBEEmbeddings.e_sigelt
                          FStar_Reflection_NBEEmbeddings.e_attributes
                         in
                      let uu____61948 =
                        let uu____61951 =
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
                        let uu____61957 =
                          let uu____61960 =
                            mk1 "inspect_binder"
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder_view
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_NBEEmbeddings.e_binder
                              FStar_Reflection_NBEEmbeddings.e_binder_view
                             in
                          let uu____61962 =
                            let uu____61965 =
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
                            let uu____61967 =
                              let uu____61970 =
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
                              let uu____61972 =
                                let uu____61975 =
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
                                let uu____61979 =
                                  let uu____61982 =
                                    let uu____61983 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Reflection_Embeddings.e_fv
                                       in
                                    let uu____61988 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Reflection_NBEEmbeddings.e_fv
                                       in
                                    mk2 "lookup_attr"
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_Embeddings.e_term
                                      FStar_Reflection_Embeddings.e_env
                                      uu____61983
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_NBEEmbeddings.e_term
                                      FStar_Reflection_NBEEmbeddings.e_env
                                      uu____61988
                                     in
                                  let uu____61998 =
                                    let uu____62001 =
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
                                    let uu____62005 =
                                      let uu____62008 =
                                        mk1 "moduleof"
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_Embeddings.e_env
                                          FStar_Syntax_Embeddings.e_string_list
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_NBEEmbeddings.e_env
                                          FStar_TypeChecker_NBETerm.e_string_list
                                         in
                                      let uu____62016 =
                                        let uu____62019 =
                                          mk1 "term_to_string"
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_string
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_NBEEmbeddings.e_term
                                            FStar_TypeChecker_NBETerm.e_string
                                           in
                                        let uu____62023 =
                                          let uu____62026 =
                                            mk1 "binders_of_env"
                                              FStar_Reflection_Basic.binders_of_env
                                              FStar_Reflection_Embeddings.e_env
                                              FStar_Reflection_Embeddings.e_binders
                                              FStar_Reflection_Basic.binders_of_env
                                              FStar_Reflection_NBEEmbeddings.e_env
                                              FStar_Reflection_NBEEmbeddings.e_binders
                                             in
                                          let uu____62028 =
                                            let uu____62031 =
                                              let uu____62032 =
                                                FStar_Syntax_Embeddings.e_option
                                                  FStar_Reflection_Embeddings.e_sigelt
                                                 in
                                              let uu____62037 =
                                                FStar_TypeChecker_NBETerm.e_option
                                                  FStar_Reflection_NBEEmbeddings.e_sigelt
                                                 in
                                              mk2 "lookup_typ"
                                                FStar_Reflection_Basic.lookup_typ
                                                FStar_Reflection_Embeddings.e_env
                                                FStar_Syntax_Embeddings.e_string_list
                                                uu____62032
                                                FStar_Reflection_Basic.lookup_typ
                                                FStar_Reflection_NBEEmbeddings.e_env
                                                FStar_TypeChecker_NBETerm.e_string_list
                                                uu____62037
                                               in
                                            [uu____62031]  in
                                          uu____62026 :: uu____62028  in
                                        uu____62019 :: uu____62023  in
                                      uu____62008 :: uu____62016  in
                                    uu____62001 :: uu____62005  in
                                  uu____61982 :: uu____61998  in
                                uu____61975 :: uu____61979  in
                              uu____61970 :: uu____61972  in
                            uu____61965 :: uu____61967  in
                          uu____61960 :: uu____61962  in
                        uu____61951 :: uu____61957  in
                      uu____61942 :: uu____61948  in
                    uu____61937 :: uu____61939  in
                  uu____61932 :: uu____61934  in
                uu____61927 :: uu____61929  in
              uu____61922 :: uu____61924  in
            uu____61917 :: uu____61919  in
          uu____61912 :: uu____61914  in
        uu____61901 :: uu____61909  in
      uu____61890 :: uu____61898  in
    uu____61885 :: uu____61887  in
  uu____61880 :: uu____61882 