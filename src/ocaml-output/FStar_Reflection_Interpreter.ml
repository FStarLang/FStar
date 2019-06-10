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
        let uu____32 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____32 true norm_cb
  
let try_unembed :
  'Auu____49 .
    'Auu____49 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____49 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____73 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____73 false norm_cb
  
let embed :
  'Auu____92 .
    'Auu____92 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____92 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea  ->
    fun r  ->
      fun x  ->
        fun norm_cb  ->
          let uu____119 = FStar_Syntax_Embeddings.embed ea x  in
          uu____119 r FStar_Pervasives_Native.None norm_cb
  
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
                | (a,uu____202)::[] ->
                    let uu____227 = try_unembed ea a n1  in
                    FStar_Util.bind_opt uu____227
                      (fun a1  ->
                         let uu____233 =
                           let uu____234 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           let uu____235 = f a1  in
                           embed er uu____234 uu____235 n1  in
                         FStar_Pervasives_Native.Some uu____233)
                | uu____236 -> FStar_Pervasives_Native.None
  
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
                  | (a,uu____330)::(b,uu____332)::[] ->
                      let uu____373 = try_unembed ea a n1  in
                      FStar_Util.bind_opt uu____373
                        (fun a1  ->
                           let uu____379 = try_unembed eb b n1  in
                           FStar_Util.bind_opt uu____379
                             (fun b1  ->
                                let uu____385 =
                                  let uu____386 =
                                    FStar_TypeChecker_Cfg.psc_range psc  in
                                  let uu____387 = f a1 b1  in
                                  embed er uu____386 uu____387 n1  in
                                FStar_Pervasives_Native.Some uu____385))
                  | uu____388 -> FStar_Pervasives_Native.None
  
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
              | (a,uu____454)::[] ->
                  let uu____463 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____463
                    (fun a1  ->
                       let uu____469 =
                         let uu____470 = f a1  in
                         FStar_TypeChecker_NBETerm.embed er cb uu____470  in
                       FStar_Pervasives_Native.Some uu____469)
              | uu____471 -> FStar_Pervasives_Native.None
  
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
                | (a,uu____556)::(b,uu____558)::[] ->
                    let uu____571 = FStar_TypeChecker_NBETerm.unembed ea cb a
                       in
                    FStar_Util.bind_opt uu____571
                      (fun a1  ->
                         let uu____577 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____577
                           (fun b1  ->
                              let uu____583 =
                                let uu____584 = f a1 b1  in
                                FStar_TypeChecker_NBETerm.embed er cb
                                  uu____584
                                 in
                              FStar_Pervasives_Native.Some uu____583))
                | uu____585 -> FStar_Pervasives_Native.None
  
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
  let uu____881 =
    mk1 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
      FStar_Reflection_Basic.inspect_ln FStar_Reflection_NBEEmbeddings.e_term
      FStar_Reflection_NBEEmbeddings.e_term_view
     in
  let uu____883 =
    let uu____886 =
      mk1 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term FStar_Reflection_Basic.pack_ln
        FStar_Reflection_NBEEmbeddings.e_term_view
        FStar_Reflection_NBEEmbeddings.e_term
       in
    let uu____888 =
      let uu____891 =
        mk1 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
          FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_NBEEmbeddings.e_fv
          FStar_TypeChecker_NBETerm.e_string_list
         in
      let uu____899 =
        let uu____902 =
          mk1 "pack_fv" FStar_Reflection_Basic.pack_fv
            FStar_Syntax_Embeddings.e_string_list
            FStar_Reflection_Embeddings.e_fv FStar_Reflection_Basic.pack_fv
            FStar_TypeChecker_NBETerm.e_string_list
            FStar_Reflection_NBEEmbeddings.e_fv
           in
        let uu____910 =
          let uu____913 =
            mk1 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
              FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_NBEEmbeddings.e_comp
              FStar_Reflection_NBEEmbeddings.e_comp_view
             in
          let uu____915 =
            let uu____918 =
              mk1 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
                FStar_Reflection_Basic.pack_comp
                FStar_Reflection_NBEEmbeddings.e_comp_view
                FStar_Reflection_NBEEmbeddings.e_comp
               in
            let uu____920 =
              let uu____923 =
                mk1 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                  FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt_view
                 in
              let uu____925 =
                let uu____928 =
                  mk1 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                    FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_NBEEmbeddings.e_sigelt_view
                    FStar_Reflection_NBEEmbeddings.e_sigelt
                   in
                let uu____930 =
                  let uu____933 =
                    mk1 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                      FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_NBEEmbeddings.e_bv
                      FStar_Reflection_NBEEmbeddings.e_bv_view
                     in
                  let uu____935 =
                    let uu____938 =
                      mk1 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                        FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_NBEEmbeddings.e_bv_view
                        FStar_Reflection_NBEEmbeddings.e_bv
                       in
                    let uu____940 =
                      let uu____943 =
                        mk1 "sigelt_attrs"
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_Embeddings.e_sigelt
                          FStar_Reflection_Embeddings.e_attributes
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_NBEEmbeddings.e_sigelt
                          FStar_Reflection_NBEEmbeddings.e_attributes
                         in
                      let uu____949 =
                        let uu____952 =
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
                        let uu____958 =
                          let uu____961 =
                            mk1 "inspect_binder"
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder_view
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_NBEEmbeddings.e_binder
                              FStar_Reflection_NBEEmbeddings.e_binder_view
                             in
                          let uu____963 =
                            let uu____966 =
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
                            let uu____968 =
                              let uu____971 =
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
                              let uu____973 =
                                let uu____976 =
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
                                let uu____980 =
                                  let uu____983 =
                                    let uu____984 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Reflection_Embeddings.e_fv
                                       in
                                    let uu____989 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Reflection_NBEEmbeddings.e_fv
                                       in
                                    mk2 "lookup_attr"
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_Embeddings.e_term
                                      FStar_Reflection_Embeddings.e_env
                                      uu____984
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_NBEEmbeddings.e_term
                                      FStar_Reflection_NBEEmbeddings.e_env
                                      uu____989
                                     in
                                  let uu____999 =
                                    let uu____1002 =
                                      let uu____1003 =
                                        FStar_Syntax_Embeddings.e_list
                                          FStar_Reflection_Embeddings.e_fv
                                         in
                                      let uu____1008 =
                                        FStar_TypeChecker_NBETerm.e_list
                                          FStar_Reflection_NBEEmbeddings.e_fv
                                         in
                                      mk1 "all_defs_in_env"
                                        FStar_Reflection_Basic.all_defs_in_env
                                        FStar_Reflection_Embeddings.e_env
                                        uu____1003
                                        FStar_Reflection_Basic.all_defs_in_env
                                        FStar_Reflection_NBEEmbeddings.e_env
                                        uu____1008
                                       in
                                    let uu____1018 =
                                      let uu____1021 =
                                        let uu____1022 =
                                          FStar_Syntax_Embeddings.e_list
                                            FStar_Reflection_Embeddings.e_fv
                                           in
                                        let uu____1027 =
                                          FStar_TypeChecker_NBETerm.e_list
                                            FStar_Reflection_NBEEmbeddings.e_fv
                                           in
                                        mk2 "defs_in_module"
                                          FStar_Reflection_Basic.defs_in_module
                                          FStar_Reflection_Embeddings.e_env
                                          FStar_Syntax_Embeddings.e_string_list
                                          uu____1022
                                          FStar_Reflection_Basic.defs_in_module
                                          FStar_Reflection_NBEEmbeddings.e_env
                                          FStar_TypeChecker_NBETerm.e_string_list
                                          uu____1027
                                         in
                                      let uu____1043 =
                                        let uu____1046 =
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
                                        let uu____1050 =
                                          let uu____1053 =
                                            mk1 "moduleof"
                                              FStar_Reflection_Basic.moduleof
                                              FStar_Reflection_Embeddings.e_env
                                              FStar_Syntax_Embeddings.e_string_list
                                              FStar_Reflection_Basic.moduleof
                                              FStar_Reflection_NBEEmbeddings.e_env
                                              FStar_TypeChecker_NBETerm.e_string_list
                                             in
                                          let uu____1061 =
                                            let uu____1064 =
                                              mk1 "term_to_string"
                                                FStar_Reflection_Basic.term_to_string
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Syntax_Embeddings.e_string
                                                FStar_Reflection_Basic.term_to_string
                                                FStar_Reflection_NBEEmbeddings.e_term
                                                FStar_TypeChecker_NBETerm.e_string
                                               in
                                            let uu____1068 =
                                              let uu____1071 =
                                                mk1 "comp_to_string"
                                                  FStar_Reflection_Basic.comp_to_string
                                                  FStar_Reflection_Embeddings.e_comp
                                                  FStar_Syntax_Embeddings.e_string
                                                  FStar_Reflection_Basic.comp_to_string
                                                  FStar_Reflection_NBEEmbeddings.e_comp
                                                  FStar_TypeChecker_NBETerm.e_string
                                                 in
                                              let uu____1075 =
                                                let uu____1078 =
                                                  mk1 "binders_of_env"
                                                    FStar_Reflection_Basic.binders_of_env
                                                    FStar_Reflection_Embeddings.e_env
                                                    FStar_Reflection_Embeddings.e_binders
                                                    FStar_Reflection_Basic.binders_of_env
                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                    FStar_Reflection_NBEEmbeddings.e_binders
                                                   in
                                                let uu____1080 =
                                                  let uu____1083 =
                                                    let uu____1084 =
                                                      FStar_Syntax_Embeddings.e_option
                                                        FStar_Reflection_Embeddings.e_sigelt
                                                       in
                                                    let uu____1089 =
                                                      FStar_TypeChecker_NBETerm.e_option
                                                        FStar_Reflection_NBEEmbeddings.e_sigelt
                                                       in
                                                    mk2 "lookup_typ"
                                                      FStar_Reflection_Basic.lookup_typ
                                                      FStar_Reflection_Embeddings.e_env
                                                      FStar_Syntax_Embeddings.e_string_list
                                                      uu____1084
                                                      FStar_Reflection_Basic.lookup_typ
                                                      FStar_Reflection_NBEEmbeddings.e_env
                                                      FStar_TypeChecker_NBETerm.e_string_list
                                                      uu____1089
                                                     in
                                                  let uu____1105 =
                                                    let uu____1108 =
                                                      let uu____1109 =
                                                        FStar_Syntax_Embeddings.e_list
                                                          FStar_Syntax_Embeddings.e_string_list
                                                         in
                                                      let uu____1120 =
                                                        FStar_TypeChecker_NBETerm.e_list
                                                          FStar_TypeChecker_NBETerm.e_string_list
                                                         in
                                                      mk1 "env_open_modules"
                                                        FStar_Reflection_Basic.env_open_modules
                                                        FStar_Reflection_Embeddings.e_env
                                                        uu____1109
                                                        FStar_Reflection_Basic.env_open_modules
                                                        FStar_Reflection_NBEEmbeddings.e_env
                                                        uu____1120
                                                       in
                                                    [uu____1108]  in
                                                  uu____1083 :: uu____1105
                                                   in
                                                uu____1078 :: uu____1080  in
                                              uu____1071 :: uu____1075  in
                                            uu____1064 :: uu____1068  in
                                          uu____1053 :: uu____1061  in
                                        uu____1046 :: uu____1050  in
                                      uu____1021 :: uu____1043  in
                                    uu____1002 :: uu____1018  in
                                  uu____983 :: uu____999  in
                                uu____976 :: uu____980  in
                              uu____971 :: uu____973  in
                            uu____966 :: uu____968  in
                          uu____961 :: uu____963  in
                        uu____952 :: uu____958  in
                      uu____943 :: uu____949  in
                    uu____938 :: uu____940  in
                  uu____933 :: uu____935  in
                uu____928 :: uu____930  in
              uu____923 :: uu____925  in
            uu____918 :: uu____920  in
          uu____913 :: uu____915  in
        uu____902 :: uu____910  in
      uu____891 :: uu____899  in
    uu____886 :: uu____888  in
  uu____881 :: uu____883 