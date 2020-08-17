open Prims
let unembed :
  'uuuuuu8 .
    'uuuuuu8 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'uuuuuu8 FStar_Pervasives_Native.option
  =
  fun ea ->
    fun a ->
      fun norm_cb ->
        let uu____32 = FStar_Syntax_Embeddings.unembed ea a in
        uu____32 true norm_cb
let try_unembed :
  'uuuuuu47 .
    'uuuuuu47 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'uuuuuu47 FStar_Pervasives_Native.option
  =
  fun ea ->
    fun a ->
      fun norm_cb ->
        let uu____71 = FStar_Syntax_Embeddings.unembed ea a in
        uu____71 false norm_cb
let embed :
  'uuuuuu88 .
    'uuuuuu88 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'uuuuuu88 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea ->
    fun r ->
      fun x ->
        fun norm_cb ->
          let uu____115 = FStar_Syntax_Embeddings.embed ea x in
          uu____115 r FStar_Pervasives_Native.None norm_cb
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
  fun m ->
    fun f ->
      fun ea ->
        fun er ->
          fun psc ->
            fun n ->
              fun args ->
                match args with
                | (a1, uu____197)::[] ->
                    let uu____222 = try_unembed ea a1 n in
                    FStar_Util.bind_opt uu____222
                      (fun a2 ->
                         let uu____228 =
                           let uu____229 =
                             FStar_TypeChecker_Cfg.psc_range psc in
                           let uu____230 = f a2 in
                           embed er uu____229 uu____230 n in
                         FStar_Pervasives_Native.Some uu____228)
                | uu____231 -> FStar_Pervasives_Native.None
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
  fun m ->
    fun f ->
      fun ea ->
        fun eb ->
          fun er ->
            fun psc ->
              fun n ->
                fun args ->
                  match args with
                  | (a1, uu____324)::(b1, uu____326)::[] ->
                      let uu____367 = try_unembed ea a1 n in
                      FStar_Util.bind_opt uu____367
                        (fun a2 ->
                           let uu____373 = try_unembed eb b1 n in
                           FStar_Util.bind_opt uu____373
                             (fun b2 ->
                                let uu____379 =
                                  let uu____380 =
                                    FStar_TypeChecker_Cfg.psc_range psc in
                                  let uu____381 = f a2 b2 in
                                  embed er uu____380 uu____381 n in
                                FStar_Pervasives_Native.Some uu____379))
                  | uu____382 -> FStar_Pervasives_Native.None
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
  fun m ->
    fun f ->
      fun ea ->
        fun er ->
          fun cb ->
            fun args ->
              match args with
              | (a1, uu____447)::[] ->
                  let uu____456 = FStar_TypeChecker_NBETerm.unembed ea cb a1 in
                  FStar_Util.bind_opt uu____456
                    (fun a2 ->
                       let uu____462 =
                         let uu____463 = f a2 in
                         FStar_TypeChecker_NBETerm.embed er cb uu____463 in
                       FStar_Pervasives_Native.Some uu____462)
              | uu____464 -> FStar_Pervasives_Native.None
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
  fun m ->
    fun f ->
      fun ea ->
        fun eb ->
          fun er ->
            fun cb ->
              fun args ->
                match args with
                | (a1, uu____548)::(b1, uu____550)::[] ->
                    let uu____563 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a1 in
                    FStar_Util.bind_opt uu____563
                      (fun a2 ->
                         let uu____569 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b1 in
                         FStar_Util.bind_opt uu____569
                           (fun b2 ->
                              let uu____575 =
                                let uu____576 = f a2 b2 in
                                FStar_TypeChecker_NBETerm.embed er cb
                                  uu____576 in
                              FStar_Pervasives_Native.Some uu____575))
                | uu____577 -> FStar_Pervasives_Native.None
let (mklid : Prims.string -> FStar_Ident.lid) =
  fun nm -> FStar_Reflection_Data.fstar_refl_builtins_lid nm
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
  fun l ->
    fun arity ->
      fun fn ->
        fun nbe_fn ->
          {
            FStar_TypeChecker_Cfg.name = l;
            FStar_TypeChecker_Cfg.arity = arity;
            FStar_TypeChecker_Cfg.univ_arity = Prims.int_zero;
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
  fun nm ->
    fun f ->
      fun ea ->
        fun er ->
          fun nf ->
            fun ena ->
              fun enr ->
                let l = mklid nm in
                mk l Prims.int_one (int1 l f ea er) (nbe_int1 l nf ena enr)
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
  fun nm ->
    fun f ->
      fun ea ->
        fun eb ->
          fun er ->
            fun nf ->
              fun ena ->
                fun enb ->
                  fun enr ->
                    let l = mklid nm in
                    mk l (Prims.of_int (2)) (int2 l f ea eb er)
                      (nbe_int2 l nf ena enb enr)
let (reflection_primops : FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  let uu____856 =
    mk1 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
      FStar_Reflection_Basic.inspect_ln FStar_Reflection_NBEEmbeddings.e_term
      FStar_Reflection_NBEEmbeddings.e_term_view in
  let uu____857 =
    let uu____860 =
      mk1 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term FStar_Reflection_Basic.pack_ln
        FStar_Reflection_NBEEmbeddings.e_term_view
        FStar_Reflection_NBEEmbeddings.e_term in
    let uu____861 =
      let uu____864 =
        mk1 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
          FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_NBEEmbeddings.e_fv
          FStar_TypeChecker_NBETerm.e_string_list in
      let uu____869 =
        let uu____872 =
          mk1 "pack_fv" FStar_Reflection_Basic.pack_fv
            FStar_Syntax_Embeddings.e_string_list
            FStar_Reflection_Embeddings.e_fv FStar_Reflection_Basic.pack_fv
            FStar_TypeChecker_NBETerm.e_string_list
            FStar_Reflection_NBEEmbeddings.e_fv in
        let uu____877 =
          let uu____880 =
            mk1 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
              FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_NBEEmbeddings.e_comp
              FStar_Reflection_NBEEmbeddings.e_comp_view in
          let uu____881 =
            let uu____884 =
              mk1 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
                FStar_Reflection_Basic.pack_comp
                FStar_Reflection_NBEEmbeddings.e_comp_view
                FStar_Reflection_NBEEmbeddings.e_comp in
            let uu____885 =
              let uu____888 =
                mk1 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                  FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt_view in
              let uu____889 =
                let uu____892 =
                  mk1 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                    FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_NBEEmbeddings.e_sigelt_view
                    FStar_Reflection_NBEEmbeddings.e_sigelt in
                let uu____893 =
                  let uu____896 =
                    mk1 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                      FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_NBEEmbeddings.e_bv
                      FStar_Reflection_NBEEmbeddings.e_bv_view in
                  let uu____897 =
                    let uu____900 =
                      mk1 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                        FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_NBEEmbeddings.e_bv_view
                        FStar_Reflection_NBEEmbeddings.e_bv in
                    let uu____901 =
                      let uu____904 =
                        let uu____905 =
                          FStar_Syntax_Embeddings.e_option
                            FStar_Reflection_Embeddings.e_term in
                        let uu____910 =
                          FStar_TypeChecker_NBETerm.e_option
                            FStar_Reflection_NBEEmbeddings.e_term in
                        mk1 "sigelt_opts" FStar_Reflection_Basic.sigelt_opts
                          FStar_Reflection_Embeddings.e_sigelt uu____905
                          FStar_Reflection_Basic.sigelt_opts
                          FStar_Reflection_NBEEmbeddings.e_sigelt uu____910 in
                      let uu____919 =
                        let uu____922 =
                          mk1 "sigelt_attrs"
                            FStar_Reflection_Basic.sigelt_attrs
                            FStar_Reflection_Embeddings.e_sigelt
                            FStar_Reflection_Embeddings.e_attributes
                            FStar_Reflection_Basic.sigelt_attrs
                            FStar_Reflection_NBEEmbeddings.e_sigelt
                            FStar_Reflection_NBEEmbeddings.e_attributes in
                        let uu____927 =
                          let uu____930 =
                            mk2 "set_sigelt_attrs"
                              FStar_Reflection_Basic.set_sigelt_attrs
                              FStar_Reflection_Embeddings.e_attributes
                              FStar_Reflection_Embeddings.e_sigelt
                              FStar_Reflection_Embeddings.e_sigelt
                              FStar_Reflection_Basic.set_sigelt_attrs
                              FStar_Reflection_NBEEmbeddings.e_attributes
                              FStar_Reflection_NBEEmbeddings.e_sigelt
                              FStar_Reflection_NBEEmbeddings.e_sigelt in
                          let uu____935 =
                            let uu____938 =
                              mk1 "sigelt_quals"
                                FStar_Reflection_Basic.sigelt_quals
                                FStar_Reflection_Embeddings.e_sigelt
                                FStar_Reflection_Embeddings.e_qualifiers
                                FStar_Reflection_Basic.sigelt_quals
                                FStar_Reflection_NBEEmbeddings.e_sigelt
                                FStar_Reflection_NBEEmbeddings.e_qualifiers in
                            let uu____943 =
                              let uu____946 =
                                mk2 "set_sigelt_quals"
                                  FStar_Reflection_Basic.set_sigelt_quals
                                  FStar_Reflection_Embeddings.e_qualifiers
                                  FStar_Reflection_Embeddings.e_sigelt
                                  FStar_Reflection_Embeddings.e_sigelt
                                  FStar_Reflection_Basic.set_sigelt_quals
                                  FStar_Reflection_NBEEmbeddings.e_qualifiers
                                  FStar_Reflection_NBEEmbeddings.e_sigelt
                                  FStar_Reflection_NBEEmbeddings.e_sigelt in
                              let uu____951 =
                                let uu____954 =
                                  mk1 "inspect_binder"
                                    FStar_Reflection_Basic.inspect_binder
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Reflection_Embeddings.e_binder_view
                                    FStar_Reflection_Basic.inspect_binder
                                    FStar_Reflection_NBEEmbeddings.e_binder
                                    FStar_Reflection_NBEEmbeddings.e_binder_view in
                                let uu____955 =
                                  let uu____958 =
                                    mk2 "pack_binder"
                                      FStar_Reflection_Basic.pack_binder
                                      FStar_Reflection_Embeddings.e_bv
                                      FStar_Reflection_Embeddings.e_aqualv
                                      FStar_Reflection_Embeddings.e_binder
                                      FStar_Reflection_Basic.pack_binder
                                      FStar_Reflection_NBEEmbeddings.e_bv
                                      FStar_Reflection_NBEEmbeddings.e_aqualv
                                      FStar_Reflection_NBEEmbeddings.e_binder in
                                  let uu____959 =
                                    let uu____962 =
                                      mk2 "compare_bv"
                                        FStar_Reflection_Basic.compare_bv
                                        FStar_Reflection_Embeddings.e_bv
                                        FStar_Reflection_Embeddings.e_bv
                                        FStar_Reflection_Embeddings.e_order
                                        FStar_Reflection_Basic.compare_bv
                                        FStar_Reflection_NBEEmbeddings.e_bv
                                        FStar_Reflection_NBEEmbeddings.e_bv
                                        FStar_Reflection_NBEEmbeddings.e_order in
                                    let uu____963 =
                                      let uu____966 =
                                        mk2 "is_free"
                                          FStar_Reflection_Basic.is_free
                                          FStar_Reflection_Embeddings.e_bv
                                          FStar_Reflection_Embeddings.e_term
                                          FStar_Syntax_Embeddings.e_bool
                                          FStar_Reflection_Basic.is_free
                                          FStar_Reflection_NBEEmbeddings.e_bv
                                          FStar_Reflection_NBEEmbeddings.e_term
                                          FStar_TypeChecker_NBETerm.e_bool in
                                      let uu____967 =
                                        let uu____970 =
                                          let uu____971 =
                                            FStar_Syntax_Embeddings.e_list
                                              FStar_Reflection_Embeddings.e_bv in
                                          let uu____976 =
                                            FStar_TypeChecker_NBETerm.e_list
                                              FStar_Reflection_NBEEmbeddings.e_bv in
                                          mk1 "free_bvs"
                                            FStar_Reflection_Basic.free_bvs
                                            FStar_Reflection_Embeddings.e_term
                                            uu____971
                                            FStar_Reflection_Basic.free_bvs
                                            FStar_Reflection_NBEEmbeddings.e_term
                                            uu____976 in
                                        let uu____985 =
                                          let uu____988 =
                                            let uu____989 =
                                              FStar_Syntax_Embeddings.e_list
                                                FStar_Syntax_Embeddings.e_int in
                                            let uu____994 =
                                              FStar_TypeChecker_NBETerm.e_list
                                                FStar_TypeChecker_NBETerm.e_int in
                                            mk1 "free_uvars"
                                              FStar_Reflection_Basic.free_uvars
                                              FStar_Reflection_Embeddings.e_term
                                              uu____989
                                              FStar_Reflection_Basic.free_uvars
                                              FStar_Reflection_NBEEmbeddings.e_term
                                              uu____994 in
                                          let uu____1003 =
                                            let uu____1006 =
                                              let uu____1007 =
                                                FStar_Syntax_Embeddings.e_list
                                                  FStar_Reflection_Embeddings.e_fv in
                                              let uu____1012 =
                                                FStar_TypeChecker_NBETerm.e_list
                                                  FStar_Reflection_NBEEmbeddings.e_fv in
                                              mk2 "lookup_attr"
                                                FStar_Reflection_Basic.lookup_attr
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Reflection_Embeddings.e_env
                                                uu____1007
                                                FStar_Reflection_Basic.lookup_attr
                                                FStar_Reflection_NBEEmbeddings.e_term
                                                FStar_Reflection_NBEEmbeddings.e_env
                                                uu____1012 in
                                            let uu____1021 =
                                              let uu____1024 =
                                                let uu____1025 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Reflection_Embeddings.e_fv in
                                                let uu____1030 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_Reflection_NBEEmbeddings.e_fv in
                                                mk1 "all_defs_in_env"
                                                  FStar_Reflection_Basic.all_defs_in_env
                                                  FStar_Reflection_Embeddings.e_env
                                                  uu____1025
                                                  FStar_Reflection_Basic.all_defs_in_env
                                                  FStar_Reflection_NBEEmbeddings.e_env
                                                  uu____1030 in
                                              let uu____1039 =
                                                let uu____1042 =
                                                  let uu____1043 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Reflection_Embeddings.e_fv in
                                                  let uu____1048 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_Reflection_NBEEmbeddings.e_fv in
                                                  mk2 "defs_in_module"
                                                    FStar_Reflection_Basic.defs_in_module
                                                    FStar_Reflection_Embeddings.e_env
                                                    FStar_Syntax_Embeddings.e_string_list
                                                    uu____1043
                                                    FStar_Reflection_Basic.defs_in_module
                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                    uu____1048 in
                                                let uu____1061 =
                                                  let uu____1064 =
                                                    mk2 "term_eq"
                                                      FStar_Reflection_Basic.term_eq
                                                      FStar_Reflection_Embeddings.e_term
                                                      FStar_Reflection_Embeddings.e_term
                                                      FStar_Syntax_Embeddings.e_bool
                                                      FStar_Reflection_Basic.term_eq
                                                      FStar_Reflection_NBEEmbeddings.e_term
                                                      FStar_Reflection_NBEEmbeddings.e_term
                                                      FStar_TypeChecker_NBETerm.e_bool in
                                                  let uu____1065 =
                                                    let uu____1068 =
                                                      mk1 "moduleof"
                                                        FStar_Reflection_Basic.moduleof
                                                        FStar_Reflection_Embeddings.e_env
                                                        FStar_Syntax_Embeddings.e_string_list
                                                        FStar_Reflection_Basic.moduleof
                                                        FStar_Reflection_NBEEmbeddings.e_env
                                                        FStar_TypeChecker_NBETerm.e_string_list in
                                                    let uu____1073 =
                                                      let uu____1076 =
                                                        mk1 "term_to_string"
                                                          FStar_Reflection_Basic.term_to_string
                                                          FStar_Reflection_Embeddings.e_term
                                                          FStar_Syntax_Embeddings.e_string
                                                          FStar_Reflection_Basic.term_to_string
                                                          FStar_Reflection_NBEEmbeddings.e_term
                                                          FStar_TypeChecker_NBETerm.e_string in
                                                      let uu____1077 =
                                                        let uu____1080 =
                                                          mk1
                                                            "comp_to_string"
                                                            FStar_Reflection_Basic.comp_to_string
                                                            FStar_Reflection_Embeddings.e_comp
                                                            FStar_Syntax_Embeddings.e_string
                                                            FStar_Reflection_Basic.comp_to_string
                                                            FStar_Reflection_NBEEmbeddings.e_comp
                                                            FStar_TypeChecker_NBETerm.e_string in
                                                        let uu____1081 =
                                                          let uu____1084 =
                                                            mk1
                                                              "binders_of_env"
                                                              FStar_Reflection_Basic.binders_of_env
                                                              FStar_Reflection_Embeddings.e_env
                                                              FStar_Reflection_Embeddings.e_binders
                                                              FStar_Reflection_Basic.binders_of_env
                                                              FStar_Reflection_NBEEmbeddings.e_env
                                                              FStar_Reflection_NBEEmbeddings.e_binders in
                                                          let uu____1085 =
                                                            let uu____1088 =
                                                              let uu____1089
                                                                =
                                                                FStar_Syntax_Embeddings.e_option
                                                                  FStar_Reflection_Embeddings.e_sigelt in
                                                              let uu____1094
                                                                =
                                                                FStar_TypeChecker_NBETerm.e_option
                                                                  FStar_Reflection_NBEEmbeddings.e_sigelt in
                                                              mk2
                                                                "lookup_typ"
                                                                FStar_Reflection_Basic.lookup_typ
                                                                FStar_Reflection_Embeddings.e_env
                                                                FStar_Syntax_Embeddings.e_string_list
                                                                uu____1089
                                                                FStar_Reflection_Basic.lookup_typ
                                                                FStar_Reflection_NBEEmbeddings.e_env
                                                                FStar_TypeChecker_NBETerm.e_string_list
                                                                uu____1094 in
                                                            let uu____1107 =
                                                              let uu____1110
                                                                =
                                                                let uu____1111
                                                                  =
                                                                  FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string_list in
                                                                let uu____1120
                                                                  =
                                                                  FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string_list in
                                                                mk1
                                                                  "env_open_modules"
                                                                  FStar_Reflection_Basic.env_open_modules
                                                                  FStar_Reflection_Embeddings.e_env
                                                                  uu____1111
                                                                  FStar_Reflection_Basic.env_open_modules
                                                                  FStar_Reflection_NBEEmbeddings.e_env
                                                                  uu____1120 in
                                                              let uu____1137
                                                                =
                                                                let uu____1140
                                                                  =
                                                                  mk1
                                                                    "implode_qn"
                                                                    FStar_Reflection_Basic.implode_qn
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Basic.implode_qn
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                let uu____1145
                                                                  =
                                                                  let uu____1148
                                                                    =
                                                                    mk1
                                                                    "explode_qn"
                                                                    FStar_Reflection_Basic.explode_qn
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    FStar_Reflection_Basic.explode_qn
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string_list in
                                                                  let uu____1153
                                                                    =
                                                                    let uu____1156
                                                                    =
                                                                    mk2
                                                                    "compare_string"
                                                                    FStar_Reflection_Basic.compare_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Reflection_Basic.compare_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    let uu____1157
                                                                    =
                                                                    let uu____1160
                                                                    =
                                                                    mk2
                                                                    "push_binder"
                                                                    FStar_Reflection_Basic.push_binder
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_binder
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Basic.push_binder
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    FStar_Reflection_NBEEmbeddings.e_binder
                                                                    FStar_Reflection_NBEEmbeddings.e_env in
                                                                    [uu____1160] in
                                                                    uu____1156
                                                                    ::
                                                                    uu____1157 in
                                                                  uu____1148
                                                                    ::
                                                                    uu____1153 in
                                                                uu____1140 ::
                                                                  uu____1145 in
                                                              uu____1110 ::
                                                                uu____1137 in
                                                            uu____1088 ::
                                                              uu____1107 in
                                                          uu____1084 ::
                                                            uu____1085 in
                                                        uu____1080 ::
                                                          uu____1081 in
                                                      uu____1076 ::
                                                        uu____1077 in
                                                    uu____1068 :: uu____1073 in
                                                  uu____1064 :: uu____1065 in
                                                uu____1042 :: uu____1061 in
                                              uu____1024 :: uu____1039 in
                                            uu____1006 :: uu____1021 in
                                          uu____988 :: uu____1003 in
                                        uu____970 :: uu____985 in
                                      uu____966 :: uu____967 in
                                    uu____962 :: uu____963 in
                                  uu____958 :: uu____959 in
                                uu____954 :: uu____955 in
                              uu____946 :: uu____951 in
                            uu____938 :: uu____943 in
                          uu____930 :: uu____935 in
                        uu____922 :: uu____927 in
                      uu____904 :: uu____919 in
                    uu____900 :: uu____901 in
                  uu____896 :: uu____897 in
                uu____892 :: uu____893 in
              uu____888 :: uu____889 in
            uu____884 :: uu____885 in
          uu____880 :: uu____881 in
        uu____872 :: uu____877 in
      uu____864 :: uu____869 in
    uu____860 :: uu____861 in
  uu____856 :: uu____857
let (uu___113 : unit) =
  FStar_List.iter FStar_TypeChecker_Cfg.register_extra_step
    reflection_primops