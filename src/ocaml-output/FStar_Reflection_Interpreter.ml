open Prims
let unembed :
  'uuuuu .
    'uuuuu FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'uuuuu FStar_Pervasives_Native.option
  =
  fun ea ->
    fun a ->
      fun norm_cb ->
        let uu___ = FStar_Syntax_Embeddings.unembed ea a in
        uu___ true norm_cb
let try_unembed :
  'uuuuu .
    'uuuuu FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'uuuuu FStar_Pervasives_Native.option
  =
  fun ea ->
    fun a ->
      fun norm_cb ->
        let uu___ = FStar_Syntax_Embeddings.unembed ea a in
        uu___ false norm_cb
let embed :
  'uuuuu .
    'uuuuu FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'uuuuu -> FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea ->
    fun r ->
      fun x ->
        fun norm_cb ->
          let uu___ = FStar_Syntax_Embeddings.embed ea x in
          uu___ r FStar_Pervasives_Native.None norm_cb
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
                | (a1, uu___)::[] ->
                    let uu___1 = try_unembed ea a1 n in
                    FStar_Util.bind_opt uu___1
                      (fun a2 ->
                         let uu___2 =
                           let uu___3 = FStar_TypeChecker_Cfg.psc_range psc in
                           let uu___4 = f a2 in embed er uu___3 uu___4 n in
                         FStar_Pervasives_Native.Some uu___2)
                | uu___ -> FStar_Pervasives_Native.None
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
                  | (a1, uu___)::(b1, uu___1)::[] ->
                      let uu___2 = try_unembed ea a1 n in
                      FStar_Util.bind_opt uu___2
                        (fun a2 ->
                           let uu___3 = try_unembed eb b1 n in
                           FStar_Util.bind_opt uu___3
                             (fun b2 ->
                                let uu___4 =
                                  let uu___5 =
                                    FStar_TypeChecker_Cfg.psc_range psc in
                                  let uu___6 = f a2 b2 in
                                  embed er uu___5 uu___6 n in
                                FStar_Pervasives_Native.Some uu___4))
                  | uu___ -> FStar_Pervasives_Native.None
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
              | (a1, uu___)::[] ->
                  let uu___1 = FStar_TypeChecker_NBETerm.unembed ea cb a1 in
                  FStar_Util.bind_opt uu___1
                    (fun a2 ->
                       let uu___2 =
                         let uu___3 = f a2 in
                         FStar_TypeChecker_NBETerm.embed er cb uu___3 in
                       FStar_Pervasives_Native.Some uu___2)
              | uu___ -> FStar_Pervasives_Native.None
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
                | (a1, uu___)::(b1, uu___1)::[] ->
                    let uu___2 = FStar_TypeChecker_NBETerm.unembed ea cb a1 in
                    FStar_Util.bind_opt uu___2
                      (fun a2 ->
                         let uu___3 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b1 in
                         FStar_Util.bind_opt uu___3
                           (fun b2 ->
                              let uu___4 =
                                let uu___5 = f a2 b2 in
                                FStar_TypeChecker_NBETerm.embed er cb uu___5 in
                              FStar_Pervasives_Native.Some uu___4))
                | uu___ -> FStar_Pervasives_Native.None
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
  let uu___ =
    mk1 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
      FStar_Reflection_Basic.inspect_ln FStar_Reflection_NBEEmbeddings.e_term
      FStar_Reflection_NBEEmbeddings.e_term_view in
  let uu___1 =
    let uu___2 =
      mk1 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term FStar_Reflection_Basic.pack_ln
        FStar_Reflection_NBEEmbeddings.e_term_view
        FStar_Reflection_NBEEmbeddings.e_term in
    let uu___3 =
      let uu___4 =
        mk1 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
          FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_NBEEmbeddings.e_fv
          FStar_TypeChecker_NBETerm.e_string_list in
      let uu___5 =
        let uu___6 =
          mk1 "pack_fv" FStar_Reflection_Basic.pack_fv
            FStar_Syntax_Embeddings.e_string_list
            FStar_Reflection_Embeddings.e_fv FStar_Reflection_Basic.pack_fv
            FStar_TypeChecker_NBETerm.e_string_list
            FStar_Reflection_NBEEmbeddings.e_fv in
        let uu___7 =
          let uu___8 =
            mk1 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
              FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_NBEEmbeddings.e_comp
              FStar_Reflection_NBEEmbeddings.e_comp_view in
          let uu___9 =
            let uu___10 =
              mk1 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
                FStar_Reflection_Basic.pack_comp
                FStar_Reflection_NBEEmbeddings.e_comp_view
                FStar_Reflection_NBEEmbeddings.e_comp in
            let uu___11 =
              let uu___12 =
                mk1 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                  FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt_view in
              let uu___13 =
                let uu___14 =
                  mk1 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                    FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_NBEEmbeddings.e_sigelt_view
                    FStar_Reflection_NBEEmbeddings.e_sigelt in
                let uu___15 =
                  let uu___16 =
                    mk1 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                      FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_NBEEmbeddings.e_bv
                      FStar_Reflection_NBEEmbeddings.e_bv_view in
                  let uu___17 =
                    let uu___18 =
                      mk1 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                        FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_NBEEmbeddings.e_bv_view
                        FStar_Reflection_NBEEmbeddings.e_bv in
                    let uu___19 =
                      let uu___20 =
                        let uu___21 =
                          FStar_Syntax_Embeddings.e_option
                            FStar_Syntax_Embeddings.e_vconfig in
                        let uu___22 =
                          FStar_TypeChecker_NBETerm.e_option
                            FStar_TypeChecker_NBETerm.e_vconfig in
                        mk1 "sigelt_opts" FStar_Reflection_Basic.sigelt_opts
                          FStar_Reflection_Embeddings.e_sigelt uu___21
                          FStar_Reflection_Basic.sigelt_opts
                          FStar_Reflection_NBEEmbeddings.e_sigelt uu___22 in
                      let uu___21 =
                        let uu___22 =
                          mk1 "embed_vconfig"
                            FStar_Reflection_Basic.embed_vconfig
                            FStar_Syntax_Embeddings.e_vconfig
                            FStar_Reflection_Embeddings.e_term
                            FStar_Reflection_Basic.embed_vconfig
                            FStar_TypeChecker_NBETerm.e_vconfig
                            FStar_Reflection_NBEEmbeddings.e_term in
                        let uu___23 =
                          let uu___24 =
                            mk1 "sigelt_attrs"
                              FStar_Reflection_Basic.sigelt_attrs
                              FStar_Reflection_Embeddings.e_sigelt
                              FStar_Reflection_Embeddings.e_attributes
                              FStar_Reflection_Basic.sigelt_attrs
                              FStar_Reflection_NBEEmbeddings.e_sigelt
                              FStar_Reflection_NBEEmbeddings.e_attributes in
                          let uu___25 =
                            let uu___26 =
                              mk2 "set_sigelt_attrs"
                                FStar_Reflection_Basic.set_sigelt_attrs
                                FStar_Reflection_Embeddings.e_attributes
                                FStar_Reflection_Embeddings.e_sigelt
                                FStar_Reflection_Embeddings.e_sigelt
                                FStar_Reflection_Basic.set_sigelt_attrs
                                FStar_Reflection_NBEEmbeddings.e_attributes
                                FStar_Reflection_NBEEmbeddings.e_sigelt
                                FStar_Reflection_NBEEmbeddings.e_sigelt in
                            let uu___27 =
                              let uu___28 =
                                mk1 "sigelt_quals"
                                  FStar_Reflection_Basic.sigelt_quals
                                  FStar_Reflection_Embeddings.e_sigelt
                                  FStar_Reflection_Embeddings.e_qualifiers
                                  FStar_Reflection_Basic.sigelt_quals
                                  FStar_Reflection_NBEEmbeddings.e_sigelt
                                  FStar_Reflection_NBEEmbeddings.e_qualifiers in
                              let uu___29 =
                                let uu___30 =
                                  mk2 "set_sigelt_quals"
                                    FStar_Reflection_Basic.set_sigelt_quals
                                    FStar_Reflection_Embeddings.e_qualifiers
                                    FStar_Reflection_Embeddings.e_sigelt
                                    FStar_Reflection_Embeddings.e_sigelt
                                    FStar_Reflection_Basic.set_sigelt_quals
                                    FStar_Reflection_NBEEmbeddings.e_qualifiers
                                    FStar_Reflection_NBEEmbeddings.e_sigelt
                                    FStar_Reflection_NBEEmbeddings.e_sigelt in
                                let uu___31 =
                                  let uu___32 =
                                    mk1 "inspect_binder"
                                      FStar_Reflection_Basic.inspect_binder
                                      FStar_Reflection_Embeddings.e_binder
                                      FStar_Reflection_Embeddings.e_binder_view
                                      FStar_Reflection_Basic.inspect_binder
                                      FStar_Reflection_NBEEmbeddings.e_binder
                                      FStar_Reflection_NBEEmbeddings.e_binder_view in
                                  let uu___33 =
                                    let uu___34 =
                                      mk2 "pack_binder"
                                        FStar_Reflection_Basic.pack_binder
                                        FStar_Reflection_Embeddings.e_bv
                                        FStar_Reflection_Embeddings.e_aqualv
                                        FStar_Reflection_Embeddings.e_binder
                                        FStar_Reflection_Basic.pack_binder
                                        FStar_Reflection_NBEEmbeddings.e_bv
                                        FStar_Reflection_NBEEmbeddings.e_aqualv
                                        FStar_Reflection_NBEEmbeddings.e_binder in
                                    let uu___35 =
                                      let uu___36 =
                                        mk2 "compare_bv"
                                          FStar_Reflection_Basic.compare_bv
                                          FStar_Reflection_Embeddings.e_bv
                                          FStar_Reflection_Embeddings.e_bv
                                          FStar_Reflection_Embeddings.e_order
                                          FStar_Reflection_Basic.compare_bv
                                          FStar_Reflection_NBEEmbeddings.e_bv
                                          FStar_Reflection_NBEEmbeddings.e_bv
                                          FStar_Reflection_NBEEmbeddings.e_order in
                                      let uu___37 =
                                        let uu___38 =
                                          mk2 "is_free"
                                            FStar_Reflection_Basic.is_free
                                            FStar_Reflection_Embeddings.e_bv
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_bool
                                            FStar_Reflection_Basic.is_free
                                            FStar_Reflection_NBEEmbeddings.e_bv
                                            FStar_Reflection_NBEEmbeddings.e_term
                                            FStar_TypeChecker_NBETerm.e_bool in
                                        let uu___39 =
                                          let uu___40 =
                                            let uu___41 =
                                              FStar_Syntax_Embeddings.e_list
                                                FStar_Reflection_Embeddings.e_bv in
                                            let uu___42 =
                                              FStar_TypeChecker_NBETerm.e_list
                                                FStar_Reflection_NBEEmbeddings.e_bv in
                                            mk1 "free_bvs"
                                              FStar_Reflection_Basic.free_bvs
                                              FStar_Reflection_Embeddings.e_term
                                              uu___41
                                              FStar_Reflection_Basic.free_bvs
                                              FStar_Reflection_NBEEmbeddings.e_term
                                              uu___42 in
                                          let uu___41 =
                                            let uu___42 =
                                              let uu___43 =
                                                FStar_Syntax_Embeddings.e_list
                                                  FStar_Syntax_Embeddings.e_int in
                                              let uu___44 =
                                                FStar_TypeChecker_NBETerm.e_list
                                                  FStar_TypeChecker_NBETerm.e_int in
                                              mk1 "free_uvars"
                                                FStar_Reflection_Basic.free_uvars
                                                FStar_Reflection_Embeddings.e_term
                                                uu___43
                                                FStar_Reflection_Basic.free_uvars
                                                FStar_Reflection_NBEEmbeddings.e_term
                                                uu___44 in
                                            let uu___43 =
                                              let uu___44 =
                                                let uu___45 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Reflection_Embeddings.e_fv in
                                                let uu___46 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_Reflection_NBEEmbeddings.e_fv in
                                                mk2 "lookup_attr"
                                                  FStar_Reflection_Basic.lookup_attr
                                                  FStar_Reflection_Embeddings.e_term
                                                  FStar_Reflection_Embeddings.e_env
                                                  uu___45
                                                  FStar_Reflection_Basic.lookup_attr
                                                  FStar_Reflection_NBEEmbeddings.e_term
                                                  FStar_Reflection_NBEEmbeddings.e_env
                                                  uu___46 in
                                              let uu___45 =
                                                let uu___46 =
                                                  let uu___47 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Reflection_Embeddings.e_fv in
                                                  let uu___48 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_Reflection_NBEEmbeddings.e_fv in
                                                  mk1 "all_defs_in_env"
                                                    FStar_Reflection_Basic.all_defs_in_env
                                                    FStar_Reflection_Embeddings.e_env
                                                    uu___47
                                                    FStar_Reflection_Basic.all_defs_in_env
                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                    uu___48 in
                                                let uu___47 =
                                                  let uu___48 =
                                                    let uu___49 =
                                                      FStar_Syntax_Embeddings.e_list
                                                        FStar_Reflection_Embeddings.e_fv in
                                                    let uu___50 =
                                                      FStar_TypeChecker_NBETerm.e_list
                                                        FStar_Reflection_NBEEmbeddings.e_fv in
                                                    mk2 "defs_in_module"
                                                      FStar_Reflection_Basic.defs_in_module
                                                      FStar_Reflection_Embeddings.e_env
                                                      FStar_Syntax_Embeddings.e_string_list
                                                      uu___49
                                                      FStar_Reflection_Basic.defs_in_module
                                                      FStar_Reflection_NBEEmbeddings.e_env
                                                      FStar_TypeChecker_NBETerm.e_string_list
                                                      uu___50 in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      mk2 "term_eq"
                                                        FStar_Reflection_Basic.term_eq
                                                        FStar_Reflection_Embeddings.e_term
                                                        FStar_Reflection_Embeddings.e_term
                                                        FStar_Syntax_Embeddings.e_bool
                                                        FStar_Reflection_Basic.term_eq
                                                        FStar_Reflection_NBEEmbeddings.e_term
                                                        FStar_Reflection_NBEEmbeddings.e_term
                                                        FStar_TypeChecker_NBETerm.e_bool in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        mk1 "moduleof"
                                                          FStar_Reflection_Basic.moduleof
                                                          FStar_Reflection_Embeddings.e_env
                                                          FStar_Syntax_Embeddings.e_string_list
                                                          FStar_Reflection_Basic.moduleof
                                                          FStar_Reflection_NBEEmbeddings.e_env
                                                          FStar_TypeChecker_NBETerm.e_string_list in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          mk1
                                                            "term_to_string"
                                                            FStar_Reflection_Basic.term_to_string
                                                            FStar_Reflection_Embeddings.e_term
                                                            FStar_Syntax_Embeddings.e_string
                                                            FStar_Reflection_Basic.term_to_string
                                                            FStar_Reflection_NBEEmbeddings.e_term
                                                            FStar_TypeChecker_NBETerm.e_string in
                                                        let uu___55 =
                                                          let uu___56 =
                                                            mk1
                                                              "comp_to_string"
                                                              FStar_Reflection_Basic.comp_to_string
                                                              FStar_Reflection_Embeddings.e_comp
                                                              FStar_Syntax_Embeddings.e_string
                                                              FStar_Reflection_Basic.comp_to_string
                                                              FStar_Reflection_NBEEmbeddings.e_comp
                                                              FStar_TypeChecker_NBETerm.e_string in
                                                          let uu___57 =
                                                            let uu___58 =
                                                              mk1
                                                                "binders_of_env"
                                                                FStar_Reflection_Basic.binders_of_env
                                                                FStar_Reflection_Embeddings.e_env
                                                                FStar_Reflection_Embeddings.e_binders
                                                                FStar_Reflection_Basic.binders_of_env
                                                                FStar_Reflection_NBEEmbeddings.e_env
                                                                FStar_Reflection_NBEEmbeddings.e_binders in
                                                            let uu___59 =
                                                              let uu___60 =
                                                                let uu___61 =
                                                                  FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_sigelt in
                                                                let uu___62 =
                                                                  FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_sigelt in
                                                                mk2
                                                                  "lookup_typ"
                                                                  FStar_Reflection_Basic.lookup_typ
                                                                  FStar_Reflection_Embeddings.e_env
                                                                  FStar_Syntax_Embeddings.e_string_list
                                                                  uu___61
                                                                  FStar_Reflection_Basic.lookup_typ
                                                                  FStar_Reflection_NBEEmbeddings.e_env
                                                                  FStar_TypeChecker_NBETerm.e_string_list
                                                                  uu___62 in
                                                              let uu___61 =
                                                                let uu___62 =
                                                                  let uu___63
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string_list in
                                                                  let uu___64
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string_list in
                                                                  mk1
                                                                    "env_open_modules"
                                                                    FStar_Reflection_Basic.env_open_modules
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu___63
                                                                    FStar_Reflection_Basic.env_open_modules
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu___64 in
                                                                let uu___63 =
                                                                  let uu___64
                                                                    =
                                                                    mk1
                                                                    "implode_qn"
                                                                    FStar_Reflection_Basic.implode_qn
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Basic.implode_qn
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                  let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    mk1
                                                                    "explode_qn"
                                                                    FStar_Reflection_Basic.explode_qn
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    FStar_Reflection_Basic.explode_qn
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string_list in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
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
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
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
                                                                    [uu___70] in
                                                                    uu___68
                                                                    ::
                                                                    uu___69 in
                                                                    uu___66
                                                                    ::
                                                                    uu___67 in
                                                                  uu___64 ::
                                                                    uu___65 in
                                                                uu___62 ::
                                                                  uu___63 in
                                                              uu___60 ::
                                                                uu___61 in
                                                            uu___58 ::
                                                              uu___59 in
                                                          uu___56 :: uu___57 in
                                                        uu___54 :: uu___55 in
                                                      uu___52 :: uu___53 in
                                                    uu___50 :: uu___51 in
                                                  uu___48 :: uu___49 in
                                                uu___46 :: uu___47 in
                                              uu___44 :: uu___45 in
                                            uu___42 :: uu___43 in
                                          uu___40 :: uu___41 in
                                        uu___38 :: uu___39 in
                                      uu___36 :: uu___37 in
                                    uu___34 :: uu___35 in
                                  uu___32 :: uu___33 in
                                uu___30 :: uu___31 in
                              uu___28 :: uu___29 in
                            uu___26 :: uu___27 in
                          uu___24 :: uu___25 in
                        uu___22 :: uu___23 in
                      uu___20 :: uu___21 in
                    uu___18 :: uu___19 in
                  uu___16 :: uu___17 in
                uu___14 :: uu___15 in
              uu___12 :: uu___13 in
            uu___10 :: uu___11 in
          uu___8 :: uu___9 in
        uu___6 :: uu___7 in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1
let (uu___113 : unit) =
  FStar_List.iter FStar_TypeChecker_Cfg.register_extra_step
    reflection_primops