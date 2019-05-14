open Prims
let unembed :
  'Auu____8 .
    'Auu____8 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____8 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____40 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____40 true norm_cb
  
let try_unembed :
  'Auu____57 .
    'Auu____57 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____57 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____89 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____89 false norm_cb
  
let embed :
  'Auu____108 .
    'Auu____108 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____108 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea  ->
    fun r  ->
      fun x  ->
        fun norm_cb  ->
          let uu____139 = FStar_Syntax_Embeddings.embed ea x  in
          uu____139 r FStar_Pervasives_Native.None norm_cb
  
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
                | (a,uu____242)::[] ->
                    let uu____283 = try_unembed ea a n1  in
                    FStar_Util.bind_opt uu____283
                      (fun a1  ->
                         let uu____293 =
                           let uu____302 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           let uu____303 = f a1  in
                           embed er uu____302 uu____303 n1  in
                         FStar_Pervasives_Native.Some uu____293)
                | uu____308 -> FStar_Pervasives_Native.None
  
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
                  | (a,uu____422)::(b,uu____424)::[] ->
                      let uu____493 = try_unembed ea a n1  in
                      FStar_Util.bind_opt uu____493
                        (fun a1  ->
                           let uu____503 = try_unembed eb b n1  in
                           FStar_Util.bind_opt uu____503
                             (fun b1  ->
                                let uu____513 =
                                  let uu____522 =
                                    FStar_TypeChecker_Cfg.psc_range psc  in
                                  let uu____523 = f a1 b1  in
                                  embed er uu____522 uu____523 n1  in
                                FStar_Pervasives_Native.Some uu____513))
                  | uu____528 -> FStar_Pervasives_Native.None
  
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
              | (a,uu____628)::[] ->
                  let uu____637 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____637
                    (fun a1  ->
                       let uu____643 =
                         let uu____644 = f a1  in
                         FStar_TypeChecker_NBETerm.embed er cb uu____644  in
                       FStar_Pervasives_Native.Some uu____643)
              | uu____645 -> FStar_Pervasives_Native.None
  
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
                | (a,uu____767)::(b,uu____769)::[] ->
                    let uu____782 = FStar_TypeChecker_NBETerm.unembed ea cb a
                       in
                    FStar_Util.bind_opt uu____782
                      (fun a1  ->
                         let uu____788 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____788
                           (fun b1  ->
                              let uu____794 =
                                let uu____795 = f a1 b1  in
                                FStar_TypeChecker_NBETerm.embed er cb
                                  uu____795
                                 in
                              FStar_Pervasives_Native.Some uu____794))
                | uu____796 -> FStar_Pervasives_Native.None
  
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
  let uu____1239 =
    mk1 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
      FStar_Reflection_Basic.inspect_ln FStar_Reflection_NBEEmbeddings.e_term
      FStar_Reflection_NBEEmbeddings.e_term_view
     in
  let uu____1273 =
    let uu____1288 =
      mk1 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term FStar_Reflection_Basic.pack_ln
        FStar_Reflection_NBEEmbeddings.e_term_view
        FStar_Reflection_NBEEmbeddings.e_term
       in
    let uu____1322 =
      let uu____1337 =
        mk1 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
          FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_NBEEmbeddings.e_fv
          FStar_TypeChecker_NBETerm.e_string_list
         in
      let uu____1375 =
        let uu____1390 =
          mk1 "pack_fv" FStar_Reflection_Basic.pack_fv
            FStar_Syntax_Embeddings.e_string_list
            FStar_Reflection_Embeddings.e_fv FStar_Reflection_Basic.pack_fv
            FStar_TypeChecker_NBETerm.e_string_list
            FStar_Reflection_NBEEmbeddings.e_fv
           in
        let uu____1428 =
          let uu____1443 =
            mk1 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
              FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_NBEEmbeddings.e_comp
              FStar_Reflection_NBEEmbeddings.e_comp_view
             in
          let uu____1477 =
            let uu____1492 =
              mk1 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
                FStar_Reflection_Basic.pack_comp
                FStar_Reflection_NBEEmbeddings.e_comp_view
                FStar_Reflection_NBEEmbeddings.e_comp
               in
            let uu____1526 =
              let uu____1541 =
                mk1 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                  FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt_view
                 in
              let uu____1577 =
                let uu____1592 =
                  mk1 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                    FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_NBEEmbeddings.e_sigelt_view
                    FStar_Reflection_NBEEmbeddings.e_sigelt
                   in
                let uu____1628 =
                  let uu____1643 =
                    mk1 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                      FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_NBEEmbeddings.e_bv
                      FStar_Reflection_NBEEmbeddings.e_bv_view
                     in
                  let uu____1685 =
                    let uu____1700 =
                      mk1 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                        FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_NBEEmbeddings.e_bv_view
                        FStar_Reflection_NBEEmbeddings.e_bv
                       in
                    let uu____1742 =
                      let uu____1757 =
                        mk1 "sigelt_attrs"
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_Embeddings.e_sigelt
                          FStar_Reflection_Embeddings.e_attributes
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_NBEEmbeddings.e_sigelt
                          FStar_Reflection_NBEEmbeddings.e_attributes
                         in
                      let uu____1805 =
                        let uu____1820 =
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
                        let uu____1878 =
                          let uu____1893 =
                            mk1 "inspect_binder"
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder_view
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_NBEEmbeddings.e_binder
                              FStar_Reflection_NBEEmbeddings.e_binder_view
                             in
                          let uu____1919 =
                            let uu____1934 =
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
                            let uu____1970 =
                              let uu____1985 =
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
                              let uu____2031 =
                                let uu____2046 =
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
                                let uu____2092 =
                                  let uu____2107 =
                                    let uu____2132 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Reflection_Embeddings.e_fv
                                       in
                                    let uu____2143 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Reflection_NBEEmbeddings.e_fv
                                       in
                                    mk2 "lookup_attr"
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_Embeddings.e_term
                                      FStar_Reflection_Embeddings.e_env
                                      uu____2132
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_NBEEmbeddings.e_term
                                      FStar_Reflection_NBEEmbeddings.e_env
                                      uu____2143
                                     in
                                  let uu____2288 =
                                    let uu____2303 =
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
                                    let uu____2347 =
                                      let uu____2362 =
                                        mk1 "moduleof"
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_Embeddings.e_env
                                          FStar_Syntax_Embeddings.e_string_list
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_NBEEmbeddings.e_env
                                          FStar_TypeChecker_NBETerm.e_string_list
                                         in
                                      let uu____2502 =
                                        let uu____2517 =
                                          mk1 "term_to_string"
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_string
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_NBEEmbeddings.e_term
                                            FStar_TypeChecker_NBETerm.e_string
                                           in
                                        let uu____2553 =
                                          let uu____2568 =
                                            mk1 "comp_to_string"
                                              FStar_Reflection_Basic.comp_to_string
                                              FStar_Reflection_Embeddings.e_comp
                                              FStar_Syntax_Embeddings.e_string
                                              FStar_Reflection_Basic.comp_to_string
                                              FStar_Reflection_NBEEmbeddings.e_comp
                                              FStar_TypeChecker_NBETerm.e_string
                                             in
                                          let uu____2604 =
                                            let uu____2619 =
                                              mk1 "binders_of_env"
                                                FStar_Reflection_Basic.binders_of_env
                                                FStar_Reflection_Embeddings.e_env
                                                FStar_Reflection_Embeddings.e_binders
                                                FStar_Reflection_Basic.binders_of_env
                                                FStar_Reflection_NBEEmbeddings.e_env
                                                FStar_Reflection_NBEEmbeddings.e_binders
                                               in
                                            let uu____2753 =
                                              let uu____2768 =
                                                let uu____2793 =
                                                  FStar_Syntax_Embeddings.e_option
                                                    FStar_Reflection_Embeddings.e_sigelt
                                                   in
                                                let uu____2808 =
                                                  FStar_TypeChecker_NBETerm.e_option
                                                    FStar_Reflection_NBEEmbeddings.e_sigelt
                                                   in
                                                mk2 "lookup_typ"
                                                  FStar_Reflection_Basic.lookup_typ
                                                  FStar_Reflection_Embeddings.e_env
                                                  FStar_Syntax_Embeddings.e_string_list
                                                  uu____2793
                                                  FStar_Reflection_Basic.lookup_typ
                                                  FStar_Reflection_NBEEmbeddings.e_env
                                                  FStar_TypeChecker_NBETerm.e_string_list
                                                  uu____2808
                                                 in
                                              let uu____2959 =
                                                let uu____2974 =
                                                  let uu____2999 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_string_list
                                                     in
                                                  let uu____3010 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_string_list
                                                     in
                                                  mk1 "env_open_modules"
                                                    FStar_Reflection_Basic.env_open_modules
                                                    FStar_Reflection_Embeddings.e_env
                                                    uu____2999
                                                    FStar_Reflection_Basic.env_open_modules
                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                    uu____3010
                                                   in
                                                [uu____2974]  in
                                              uu____2768 :: uu____2959  in
                                            uu____2619 :: uu____2753  in
                                          uu____2568 :: uu____2604  in
                                        uu____2517 :: uu____2553  in
                                      uu____2362 :: uu____2502  in
                                    uu____2303 :: uu____2347  in
                                  uu____2107 :: uu____2288  in
                                uu____2046 :: uu____2092  in
                              uu____1985 :: uu____2031  in
                            uu____1934 :: uu____1970  in
                          uu____1893 :: uu____1919  in
                        uu____1820 :: uu____1878  in
                      uu____1757 :: uu____1805  in
                    uu____1700 :: uu____1742  in
                  uu____1643 :: uu____1685  in
                uu____1592 :: uu____1628  in
              uu____1541 :: uu____1577  in
            uu____1492 :: uu____1526  in
          uu____1443 :: uu____1477  in
        uu____1390 :: uu____1428  in
      uu____1337 :: uu____1375  in
    uu____1288 :: uu____1322  in
  uu____1239 :: uu____1273 