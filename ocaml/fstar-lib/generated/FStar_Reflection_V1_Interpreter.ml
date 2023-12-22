open Prims
let mk1 :
  'res 't1 .
    Prims.string ->
      't1 FStar_Syntax_Embeddings_Base.embedding ->
        'res FStar_Syntax_Embeddings_Base.embedding ->
          't1 FStar_TypeChecker_NBETerm.embedding ->
            'res FStar_TypeChecker_NBETerm.embedding ->
              ('t1 -> 'res) -> FStar_TypeChecker_Primops_Base.primitive_step
  =
  fun nm ->
    fun uu___ ->
      fun uu___1 ->
        fun uu___2 ->
          fun uu___3 ->
            fun f ->
              let lid =
                FStar_Reflection_V1_Constants.fstar_refl_builtins_lid nm in
              FStar_TypeChecker_Primops_Base.mk1' Prims.int_zero lid uu___
                uu___2 uu___1 uu___3
                (fun x ->
                   let uu___4 = f x in FStar_Pervasives_Native.Some uu___4)
                (fun x ->
                   let uu___4 = f x in FStar_Pervasives_Native.Some uu___4)
let mk2 :
  'res 't1 't2 .
    Prims.string ->
      't1 FStar_Syntax_Embeddings_Base.embedding ->
        't2 FStar_Syntax_Embeddings_Base.embedding ->
          'res FStar_Syntax_Embeddings_Base.embedding ->
            't1 FStar_TypeChecker_NBETerm.embedding ->
              't2 FStar_TypeChecker_NBETerm.embedding ->
                'res FStar_TypeChecker_NBETerm.embedding ->
                  ('t1 -> 't2 -> 'res) ->
                    FStar_TypeChecker_Primops_Base.primitive_step
  =
  fun nm ->
    fun uu___ ->
      fun uu___1 ->
        fun uu___2 ->
          fun uu___3 ->
            fun uu___4 ->
              fun uu___5 ->
                fun f ->
                  let lid =
                    FStar_Reflection_V1_Constants.fstar_refl_builtins_lid nm in
                  FStar_TypeChecker_Primops_Base.mk2' Prims.int_zero lid
                    uu___ uu___3 uu___1 uu___4 uu___2 uu___5
                    (fun x ->
                       fun y ->
                         let uu___6 = f x y in
                         FStar_Pervasives_Native.Some uu___6)
                    (fun x ->
                       fun y ->
                         let uu___6 = f x y in
                         FStar_Pervasives_Native.Some uu___6)
let mk3 :
  'res 't1 't2 't3 .
    Prims.string ->
      't1 FStar_Syntax_Embeddings_Base.embedding ->
        't2 FStar_Syntax_Embeddings_Base.embedding ->
          't3 FStar_Syntax_Embeddings_Base.embedding ->
            'res FStar_Syntax_Embeddings_Base.embedding ->
              't1 FStar_TypeChecker_NBETerm.embedding ->
                't2 FStar_TypeChecker_NBETerm.embedding ->
                  't3 FStar_TypeChecker_NBETerm.embedding ->
                    'res FStar_TypeChecker_NBETerm.embedding ->
                      ('t1 -> 't2 -> 't3 -> 'res) ->
                        FStar_TypeChecker_Primops_Base.primitive_step
  =
  fun nm ->
    fun uu___ ->
      fun uu___1 ->
        fun uu___2 ->
          fun uu___3 ->
            fun uu___4 ->
              fun uu___5 ->
                fun uu___6 ->
                  fun uu___7 ->
                    fun f ->
                      let lid =
                        FStar_Reflection_V1_Constants.fstar_refl_builtins_lid
                          nm in
                      FStar_TypeChecker_Primops_Base.mk3' Prims.int_zero lid
                        uu___ uu___4 uu___1 uu___5 uu___2 uu___6 uu___3
                        uu___7
                        (fun x ->
                           fun y ->
                             fun z ->
                               let uu___8 = f x y z in
                               FStar_Pervasives_Native.Some uu___8)
                        (fun x ->
                           fun y ->
                             fun z ->
                               let uu___8 = f x y z in
                               FStar_Pervasives_Native.Some uu___8)
let (uu___60 :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_term
let (uu___61 :
  FStar_Reflection_V1_Data.term_view FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_term_view
let (uu___62 : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_fv
let (uu___63 : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_bv
let (uu___64 :
  FStar_Reflection_V1_Data.bv_view FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_bv_view
let (uu___65 :
  FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_comp
let (uu___66 :
  FStar_Reflection_V1_Data.comp_view FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_comp_view
let (uu___67 :
  FStar_Syntax_Syntax.universe FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_universe
let (uu___68 :
  FStar_Reflection_V1_Data.universe_view
    FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_universe_view
let (uu___69 :
  FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_sigelt
let (uu___70 :
  FStar_Reflection_V1_Data.sigelt_view FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_sigelt_view
let (uu___71 :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_binder
let (uu___72 :
  FStar_Reflection_V1_Data.binder_view FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_binder_view
let (uu___73 :
  FStar_Reflection_V1_Data.binders FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_binders
let (uu___74 :
  FStar_Syntax_Syntax.letbinding FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_letbinding
let (uu___75 :
  FStar_Reflection_V1_Data.lb_view FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_lb_view
let (uu___76 :
  FStar_TypeChecker_Env.env FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_env
let (uu___77 :
  FStar_Reflection_V1_Data.aqualv FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_aqualv
let (uu___78 :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_attributes
let (uu___79 :
  FStar_Reflection_V1_Data.qualifier Prims.list
    FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_qualifiers
let (uu___80 : FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_term
let (uu___81 :
  FStar_Reflection_V1_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_term_view
let (uu___82 : FStar_Syntax_Syntax.fv FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_fv
let (uu___83 : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_bv
let (uu___84 :
  FStar_Reflection_V1_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_bv_view
let (uu___85 : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_comp
let (uu___86 :
  FStar_Reflection_V1_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_comp_view
let (uu___87 :
  FStar_Syntax_Syntax.universe FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_universe
let (uu___88 :
  FStar_Reflection_V1_Data.universe_view FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_universe_view
let (uu___89 :
  FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_sigelt
let (uu___90 :
  FStar_Reflection_V1_Data.sigelt_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_sigelt_view
let (uu___91 :
  FStar_Syntax_Syntax.binder FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_binder
let (uu___92 :
  FStar_Reflection_V1_Data.binder_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_binder_view
let (uu___93 :
  FStar_Reflection_V1_Data.binders FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_binders
let (uu___94 :
  FStar_Syntax_Syntax.letbinding FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_letbinding
let (uu___95 :
  FStar_Reflection_V1_Data.lb_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_lb_view
let (uu___96 : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_env
let (uu___97 :
  FStar_Reflection_V1_Data.aqualv FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_aqualv
let (uu___98 :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_attributes
let (uu___99 :
  FStar_Reflection_V1_Data.qualifier Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_qualifiers
let (reflection_primops :
  FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    mk1 "inspect_ln" uu___60 uu___61 uu___80 uu___81
      FStar_Reflection_V1_Builtins.inspect_ln in
  let uu___1 =
    let uu___2 =
      mk1 "pack_ln" uu___61 uu___60 uu___81 uu___80
        FStar_Reflection_V1_Builtins.pack_ln in
    let uu___3 =
      let uu___4 =
        mk1 "inspect_fv" uu___62 FStar_Syntax_Embeddings.e_string_list
          uu___82 FStar_TypeChecker_NBETerm.e_string_list
          FStar_Reflection_V1_Builtins.inspect_fv in
      let uu___5 =
        let uu___6 =
          mk1 "pack_fv" FStar_Syntax_Embeddings.e_string_list uu___62
            FStar_TypeChecker_NBETerm.e_string_list uu___82
            FStar_Reflection_V1_Builtins.pack_fv in
        let uu___7 =
          let uu___8 =
            mk1 "inspect_comp" uu___65 uu___66 uu___85 uu___86
              FStar_Reflection_V1_Builtins.inspect_comp in
          let uu___9 =
            let uu___10 =
              mk1 "pack_comp" uu___66 uu___65 uu___86 uu___85
                FStar_Reflection_V1_Builtins.pack_comp in
            let uu___11 =
              let uu___12 =
                mk1 "inspect_universe" uu___67 uu___68 uu___87 uu___88
                  FStar_Reflection_V1_Builtins.inspect_universe in
              let uu___13 =
                let uu___14 =
                  mk1 "pack_universe" uu___68 uu___67 uu___88 uu___87
                    FStar_Reflection_V1_Builtins.pack_universe in
                let uu___15 =
                  let uu___16 =
                    mk1 "inspect_sigelt" uu___69 uu___70 uu___89 uu___90
                      FStar_Reflection_V1_Builtins.inspect_sigelt in
                  let uu___17 =
                    let uu___18 =
                      mk1 "pack_sigelt" uu___70 uu___69 uu___90 uu___89
                        FStar_Reflection_V1_Builtins.pack_sigelt in
                    let uu___19 =
                      let uu___20 =
                        mk1 "inspect_lb" uu___74 uu___75 uu___94 uu___95
                          FStar_Reflection_V1_Builtins.inspect_lb in
                      let uu___21 =
                        let uu___22 =
                          mk1 "pack_lb" uu___75 uu___74 uu___95 uu___94
                            FStar_Reflection_V1_Builtins.pack_lb in
                        let uu___23 =
                          let uu___24 =
                            mk1 "inspect_bv" uu___63 uu___64 uu___83 uu___84
                              FStar_Reflection_V1_Builtins.inspect_bv in
                          let uu___25 =
                            let uu___26 =
                              mk1 "pack_bv" uu___64 uu___63 uu___84 uu___83
                                FStar_Reflection_V1_Builtins.pack_bv in
                            let uu___27 =
                              let uu___28 =
                                mk1 "inspect_binder" uu___71 uu___72 uu___91
                                  uu___92
                                  FStar_Reflection_V1_Builtins.inspect_binder in
                              let uu___29 =
                                let uu___30 =
                                  mk1 "pack_binder" uu___72 uu___71 uu___92
                                    uu___91
                                    FStar_Reflection_V1_Builtins.pack_binder in
                                let uu___31 =
                                  let uu___32 =
                                    mk1 "sigelt_opts" uu___69
                                      (FStar_Syntax_Embeddings.e_option
                                         FStar_Syntax_Embeddings.e_vconfig)
                                      uu___89
                                      (FStar_TypeChecker_NBETerm.e_option
                                         FStar_TypeChecker_NBETerm.e_vconfig)
                                      FStar_Reflection_V1_Builtins.sigelt_opts in
                                  let uu___33 =
                                    let uu___34 =
                                      mk1 "embed_vconfig"
                                        FStar_Syntax_Embeddings.e_vconfig
                                        uu___60
                                        FStar_TypeChecker_NBETerm.e_vconfig
                                        uu___80
                                        FStar_Reflection_V1_Builtins.embed_vconfig in
                                    let uu___35 =
                                      let uu___36 =
                                        mk1 "sigelt_attrs" uu___69 uu___78
                                          uu___89 uu___98
                                          FStar_Reflection_V1_Builtins.sigelt_attrs in
                                      let uu___37 =
                                        let uu___38 =
                                          mk2 "set_sigelt_attrs" uu___78
                                            uu___69 uu___69 uu___98 uu___89
                                            uu___89
                                            FStar_Reflection_V1_Builtins.set_sigelt_attrs in
                                        let uu___39 =
                                          let uu___40 =
                                            mk1 "sigelt_quals" uu___69
                                              uu___79 uu___89 uu___99
                                              FStar_Reflection_V1_Builtins.sigelt_quals in
                                          let uu___41 =
                                            let uu___42 =
                                              mk2 "set_sigelt_quals" uu___79
                                                uu___69 uu___69 uu___99
                                                uu___89 uu___89
                                                FStar_Reflection_V1_Builtins.set_sigelt_quals in
                                            let uu___43 =
                                              let uu___44 =
                                                mk3 "subst" uu___63 uu___60
                                                  uu___60 uu___60 uu___83
                                                  uu___80 uu___80 uu___80
                                                  FStar_Reflection_V1_Builtins.subst in
                                              let uu___45 =
                                                let uu___46 =
                                                  mk2 "close_term" uu___71
                                                    uu___60 uu___60 uu___91
                                                    uu___80 uu___80
                                                    FStar_Reflection_V1_Builtins.close_term in
                                                let uu___47 =
                                                  let uu___48 =
                                                    mk2 "compare_bv" uu___63
                                                      uu___63
                                                      FStar_Syntax_Embeddings.e_order
                                                      uu___83 uu___83
                                                      FStar_TypeChecker_NBETerm.e_order
                                                      FStar_Reflection_V1_Builtins.compare_bv in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      mk2 "lookup_attr"
                                                        uu___60 uu___76
                                                        (FStar_Syntax_Embeddings.e_list
                                                           uu___62) uu___80
                                                        uu___96
                                                        (FStar_TypeChecker_NBETerm.e_list
                                                           uu___82)
                                                        FStar_Reflection_V1_Builtins.lookup_attr in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        mk1 "all_defs_in_env"
                                                          uu___76
                                                          (FStar_Syntax_Embeddings.e_list
                                                             uu___62) uu___96
                                                          (FStar_TypeChecker_NBETerm.e_list
                                                             uu___82)
                                                          FStar_Reflection_V1_Builtins.all_defs_in_env in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          mk2
                                                            "defs_in_module"
                                                            uu___76
                                                            FStar_Syntax_Embeddings.e_string_list
                                                            (FStar_Syntax_Embeddings.e_list
                                                               uu___62)
                                                            uu___96
                                                            FStar_TypeChecker_NBETerm.e_string_list
                                                            (FStar_TypeChecker_NBETerm.e_list
                                                               uu___82)
                                                            FStar_Reflection_V1_Builtins.defs_in_module in
                                                        let uu___55 =
                                                          let uu___56 =
                                                            mk2 "term_eq"
                                                              uu___60 uu___60
                                                              FStar_Syntax_Embeddings.e_bool
                                                              uu___80 uu___80
                                                              FStar_TypeChecker_NBETerm.e_bool
                                                              FStar_Reflection_V1_Builtins.term_eq in
                                                          let uu___57 =
                                                            let uu___58 =
                                                              mk1 "moduleof"
                                                                uu___76
                                                                FStar_Syntax_Embeddings.e_string_list
                                                                uu___96
                                                                FStar_TypeChecker_NBETerm.e_string_list
                                                                FStar_Reflection_V1_Builtins.moduleof in
                                                            let uu___59 =
                                                              let uu___100 =
                                                                mk1
                                                                  "binders_of_env"
                                                                  uu___76
                                                                  uu___73
                                                                  uu___96
                                                                  uu___93
                                                                  FStar_Reflection_V1_Builtins.binders_of_env in
                                                              let uu___101 =
                                                                let uu___102
                                                                  =
                                                                  mk2
                                                                    "lookup_typ"
                                                                    uu___76
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    (
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    uu___69)
                                                                    uu___96
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    (
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    uu___89)
                                                                    FStar_Reflection_V1_Builtins.lookup_typ in
                                                                let uu___103
                                                                  =
                                                                  let uu___104
                                                                    =
                                                                    mk1
                                                                    "env_open_modules"
                                                                    uu___76
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string_list)
                                                                    uu___96
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string_list)
                                                                    FStar_Reflection_V1_Builtins.env_open_modules in
                                                                  let uu___105
                                                                    =
                                                                    let uu___106
                                                                    =
                                                                    mk1
                                                                    "implode_qn"
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Reflection_V1_Builtins.implode_qn in
                                                                    let uu___107
                                                                    =
                                                                    let uu___108
                                                                    =
                                                                    mk1
                                                                    "explode_qn"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    FStar_Reflection_V1_Builtins.explode_qn in
                                                                    let uu___109
                                                                    =
                                                                    let uu___110
                                                                    =
                                                                    mk2
                                                                    "compare_string"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Reflection_V1_Builtins.compare_string in
                                                                    let uu___111
                                                                    =
                                                                    let uu___112
                                                                    =
                                                                    mk2
                                                                    "push_binder"
                                                                    uu___76
                                                                    uu___71
                                                                    uu___76
                                                                    uu___96
                                                                    uu___91
                                                                    uu___96
                                                                    FStar_Reflection_V1_Builtins.push_binder in
                                                                    let uu___113
                                                                    =
                                                                    let uu___114
                                                                    =
                                                                    mk1
                                                                    "range_of_term"
                                                                    uu___60
                                                                    FStar_Syntax_Embeddings.e_range
                                                                    uu___80
                                                                    FStar_TypeChecker_NBETerm.e_range
                                                                    FStar_Reflection_V1_Builtins.range_of_term in
                                                                    let uu___115
                                                                    =
                                                                    let uu___116
                                                                    =
                                                                    mk1
                                                                    "range_of_sigelt"
                                                                    uu___69
                                                                    FStar_Syntax_Embeddings.e_range
                                                                    uu___89
                                                                    FStar_TypeChecker_NBETerm.e_range
                                                                    FStar_Reflection_V1_Builtins.range_of_sigelt in
                                                                    [uu___116] in
                                                                    uu___114
                                                                    ::
                                                                    uu___115 in
                                                                    uu___112
                                                                    ::
                                                                    uu___113 in
                                                                    uu___110
                                                                    ::
                                                                    uu___111 in
                                                                    uu___108
                                                                    ::
                                                                    uu___109 in
                                                                    uu___106
                                                                    ::
                                                                    uu___107 in
                                                                  uu___104 ::
                                                                    uu___105 in
                                                                uu___102 ::
                                                                  uu___103 in
                                                              uu___100 ::
                                                                uu___101 in
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
let (uu___100 : unit) =
  FStar_Compiler_List.iter FStar_TypeChecker_Cfg.register_extra_step
    reflection_primops