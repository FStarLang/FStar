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
let (uu___0 :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_term
let (uu___1 :
  FStar_Reflection_V1_Data.term_view FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_term_view
let (uu___2 : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_fv
let (uu___3 : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_bv
let (uu___4 :
  FStar_Reflection_V1_Data.bv_view FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_bv_view
let (uu___5 :
  FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_comp
let (uu___6 :
  FStar_Reflection_V1_Data.comp_view FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_comp_view
let (uu___7 :
  FStar_Syntax_Syntax.universe FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_universe
let (uu___8 :
  FStar_Reflection_V1_Data.universe_view
    FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_universe_view
let (uu___9 :
  FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_sigelt
let (uu___10 :
  FStar_Reflection_V1_Data.sigelt_view FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_sigelt_view
let (uu___11 :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_binder
let (uu___12 :
  FStar_Reflection_V1_Data.binder_view FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_binder_view
let (uu___13 :
  FStar_Reflection_V1_Data.binders FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_binders
let (uu___14 :
  FStar_Syntax_Syntax.letbinding FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_letbinding
let (uu___15 :
  FStar_Reflection_V1_Data.lb_view FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_lb_view
let (uu___16 :
  FStar_TypeChecker_Env.env FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_env
let (uu___17 :
  FStar_Reflection_V1_Data.aqualv FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_aqualv
let (uu___18 :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_attributes
let (uu___19 :
  FStar_Reflection_V1_Data.qualifier Prims.list
    FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V1_Embeddings.e_qualifiers
let (uu___20 : FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_term
let (uu___21 :
  FStar_Reflection_V1_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_term_view
let (uu___22 : FStar_Syntax_Syntax.fv FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_fv
let (uu___23 : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_bv
let (uu___24 :
  FStar_Reflection_V1_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_bv_view
let (uu___25 : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_comp
let (uu___26 :
  FStar_Reflection_V1_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_comp_view
let (uu___27 :
  FStar_Syntax_Syntax.universe FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_universe
let (uu___28 :
  FStar_Reflection_V1_Data.universe_view FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_universe_view
let (uu___29 :
  FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_sigelt
let (uu___30 :
  FStar_Reflection_V1_Data.sigelt_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_sigelt_view
let (uu___31 :
  FStar_Syntax_Syntax.binder FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_binder
let (uu___32 :
  FStar_Reflection_V1_Data.binder_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_binder_view
let (uu___33 :
  FStar_Reflection_V1_Data.binders FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_binders
let (uu___34 :
  FStar_Syntax_Syntax.letbinding FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_letbinding
let (uu___35 :
  FStar_Reflection_V1_Data.lb_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_lb_view
let (uu___36 : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_env
let (uu___37 :
  FStar_Reflection_V1_Data.aqualv FStar_TypeChecker_NBETerm.embedding) =
  FStar_Reflection_V1_NBEEmbeddings.e_aqualv
let (uu___38 :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_attributes
let (uu___39 :
  FStar_Reflection_V1_Data.qualifier Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_Reflection_V1_NBEEmbeddings.e_qualifiers
let (reflection_primops :
  FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    mk1 "inspect_ln" uu___0 uu___1 uu___20 uu___21
      FStar_Reflection_V1_Builtins.inspect_ln in
  let uu___40 =
    let uu___41 =
      mk1 "pack_ln" uu___1 uu___0 uu___21 uu___20
        FStar_Reflection_V1_Builtins.pack_ln in
    let uu___42 =
      let uu___43 =
        mk1 "inspect_fv" uu___2 FStar_Syntax_Embeddings.e_string_list uu___22
          FStar_TypeChecker_NBETerm.e_string_list
          FStar_Reflection_V1_Builtins.inspect_fv in
      let uu___44 =
        let uu___45 =
          mk1 "pack_fv" FStar_Syntax_Embeddings.e_string_list uu___2
            FStar_TypeChecker_NBETerm.e_string_list uu___22
            FStar_Reflection_V1_Builtins.pack_fv in
        let uu___46 =
          let uu___47 =
            mk1 "inspect_comp" uu___5 uu___6 uu___25 uu___26
              FStar_Reflection_V1_Builtins.inspect_comp in
          let uu___48 =
            let uu___49 =
              mk1 "pack_comp" uu___6 uu___5 uu___26 uu___25
                FStar_Reflection_V1_Builtins.pack_comp in
            let uu___50 =
              let uu___51 =
                mk1 "inspect_universe" uu___7 uu___8 uu___27 uu___28
                  FStar_Reflection_V1_Builtins.inspect_universe in
              let uu___52 =
                let uu___53 =
                  mk1 "pack_universe" uu___8 uu___7 uu___28 uu___27
                    FStar_Reflection_V1_Builtins.pack_universe in
                let uu___54 =
                  let uu___55 =
                    mk1 "inspect_sigelt" uu___9 uu___10 uu___29 uu___30
                      FStar_Reflection_V1_Builtins.inspect_sigelt in
                  let uu___56 =
                    let uu___57 =
                      mk1 "pack_sigelt" uu___10 uu___9 uu___30 uu___29
                        FStar_Reflection_V1_Builtins.pack_sigelt in
                    let uu___58 =
                      let uu___59 =
                        mk1 "inspect_lb" uu___14 uu___15 uu___34 uu___35
                          FStar_Reflection_V1_Builtins.inspect_lb in
                      let uu___60 =
                        let uu___61 =
                          mk1 "pack_lb" uu___15 uu___14 uu___35 uu___34
                            FStar_Reflection_V1_Builtins.pack_lb in
                        let uu___62 =
                          let uu___63 =
                            mk1 "inspect_bv" uu___3 uu___4 uu___23 uu___24
                              FStar_Reflection_V1_Builtins.inspect_bv in
                          let uu___64 =
                            let uu___65 =
                              mk1 "pack_bv" uu___4 uu___3 uu___24 uu___23
                                FStar_Reflection_V1_Builtins.pack_bv in
                            let uu___66 =
                              let uu___67 =
                                mk1 "inspect_binder" uu___11 uu___12 uu___31
                                  uu___32
                                  FStar_Reflection_V1_Builtins.inspect_binder in
                              let uu___68 =
                                let uu___69 =
                                  mk1 "pack_binder" uu___12 uu___11 uu___32
                                    uu___31
                                    FStar_Reflection_V1_Builtins.pack_binder in
                                let uu___70 =
                                  let uu___71 =
                                    mk1 "sigelt_opts" uu___9
                                      (FStar_Syntax_Embeddings.e_option
                                         FStar_Syntax_Embeddings.e_vconfig)
                                      uu___29
                                      (FStar_TypeChecker_NBETerm.e_option
                                         FStar_TypeChecker_NBETerm.e_vconfig)
                                      FStar_Reflection_V1_Builtins.sigelt_opts in
                                  let uu___72 =
                                    let uu___73 =
                                      mk1 "embed_vconfig"
                                        FStar_Syntax_Embeddings.e_vconfig
                                        uu___0
                                        FStar_TypeChecker_NBETerm.e_vconfig
                                        uu___20
                                        FStar_Reflection_V1_Builtins.embed_vconfig in
                                    let uu___74 =
                                      let uu___75 =
                                        mk1 "sigelt_attrs" uu___9 uu___18
                                          uu___29 uu___38
                                          FStar_Reflection_V1_Builtins.sigelt_attrs in
                                      let uu___76 =
                                        let uu___77 =
                                          mk2 "set_sigelt_attrs" uu___18
                                            uu___9 uu___9 uu___38 uu___29
                                            uu___29
                                            FStar_Reflection_V1_Builtins.set_sigelt_attrs in
                                        let uu___78 =
                                          let uu___79 =
                                            mk1 "sigelt_quals" uu___9 uu___19
                                              uu___29 uu___39
                                              FStar_Reflection_V1_Builtins.sigelt_quals in
                                          let uu___80 =
                                            let uu___81 =
                                              mk2 "set_sigelt_quals" uu___19
                                                uu___9 uu___9 uu___39 uu___29
                                                uu___29
                                                FStar_Reflection_V1_Builtins.set_sigelt_quals in
                                            let uu___82 =
                                              let uu___83 =
                                                mk3 "subst" uu___3 uu___0
                                                  uu___0 uu___0 uu___23
                                                  uu___20 uu___20 uu___20
                                                  FStar_Reflection_V1_Builtins.subst in
                                              let uu___84 =
                                                let uu___85 =
                                                  mk2 "close_term" uu___11
                                                    uu___0 uu___0 uu___31
                                                    uu___20 uu___20
                                                    FStar_Reflection_V1_Builtins.close_term in
                                                let uu___86 =
                                                  let uu___87 =
                                                    mk2 "compare_bv" uu___3
                                                      uu___3
                                                      FStar_Syntax_Embeddings.e_order
                                                      uu___23 uu___23
                                                      FStar_TypeChecker_NBETerm.e_order
                                                      FStar_Reflection_V1_Builtins.compare_bv in
                                                  let uu___88 =
                                                    let uu___89 =
                                                      mk2 "lookup_attr"
                                                        uu___0 uu___16
                                                        (FStar_Syntax_Embeddings.e_list
                                                           uu___2) uu___20
                                                        uu___36
                                                        (FStar_TypeChecker_NBETerm.e_list
                                                           uu___22)
                                                        FStar_Reflection_V1_Builtins.lookup_attr in
                                                    let uu___90 =
                                                      let uu___91 =
                                                        mk1 "all_defs_in_env"
                                                          uu___16
                                                          (FStar_Syntax_Embeddings.e_list
                                                             uu___2) uu___36
                                                          (FStar_TypeChecker_NBETerm.e_list
                                                             uu___22)
                                                          FStar_Reflection_V1_Builtins.all_defs_in_env in
                                                      let uu___92 =
                                                        let uu___93 =
                                                          mk2
                                                            "defs_in_module"
                                                            uu___16
                                                            FStar_Syntax_Embeddings.e_string_list
                                                            (FStar_Syntax_Embeddings.e_list
                                                               uu___2)
                                                            uu___36
                                                            FStar_TypeChecker_NBETerm.e_string_list
                                                            (FStar_TypeChecker_NBETerm.e_list
                                                               uu___22)
                                                            FStar_Reflection_V1_Builtins.defs_in_module in
                                                        let uu___94 =
                                                          let uu___95 =
                                                            mk2 "term_eq"
                                                              uu___0 uu___0
                                                              FStar_Syntax_Embeddings.e_bool
                                                              uu___20 uu___20
                                                              FStar_TypeChecker_NBETerm.e_bool
                                                              FStar_Reflection_V1_Builtins.term_eq in
                                                          let uu___96 =
                                                            let uu___97 =
                                                              mk1 "moduleof"
                                                                uu___16
                                                                FStar_Syntax_Embeddings.e_string_list
                                                                uu___36
                                                                FStar_TypeChecker_NBETerm.e_string_list
                                                                FStar_Reflection_V1_Builtins.moduleof in
                                                            let uu___98 =
                                                              let uu___99 =
                                                                mk1
                                                                  "binders_of_env"
                                                                  uu___16
                                                                  uu___13
                                                                  uu___36
                                                                  uu___33
                                                                  FStar_Reflection_V1_Builtins.binders_of_env in
                                                              let uu___100 =
                                                                let uu___101
                                                                  =
                                                                  mk2
                                                                    "lookup_typ"
                                                                    uu___16
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    (
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    uu___9)
                                                                    uu___36
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    (
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    uu___29)
                                                                    FStar_Reflection_V1_Builtins.lookup_typ in
                                                                let uu___102
                                                                  =
                                                                  let uu___103
                                                                    =
                                                                    mk1
                                                                    "env_open_modules"
                                                                    uu___16
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string_list)
                                                                    uu___36
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string_list)
                                                                    FStar_Reflection_V1_Builtins.env_open_modules in
                                                                  let uu___104
                                                                    =
                                                                    let uu___105
                                                                    =
                                                                    mk1
                                                                    "implode_qn"
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Reflection_V1_Builtins.implode_qn in
                                                                    let uu___106
                                                                    =
                                                                    let uu___107
                                                                    =
                                                                    mk1
                                                                    "explode_qn"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    FStar_Reflection_V1_Builtins.explode_qn in
                                                                    let uu___108
                                                                    =
                                                                    let uu___109
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
                                                                    let uu___110
                                                                    =
                                                                    let uu___111
                                                                    =
                                                                    mk2
                                                                    "push_binder"
                                                                    uu___16
                                                                    uu___11
                                                                    uu___16
                                                                    uu___36
                                                                    uu___31
                                                                    uu___36
                                                                    FStar_Reflection_V1_Builtins.push_binder in
                                                                    let uu___112
                                                                    =
                                                                    let uu___113
                                                                    =
                                                                    mk1
                                                                    "range_of_term"
                                                                    uu___0
                                                                    FStar_Syntax_Embeddings.e_range
                                                                    uu___20
                                                                    FStar_TypeChecker_NBETerm.e_range
                                                                    FStar_Reflection_V1_Builtins.range_of_term in
                                                                    let uu___114
                                                                    =
                                                                    let uu___115
                                                                    =
                                                                    mk1
                                                                    "range_of_sigelt"
                                                                    uu___9
                                                                    FStar_Syntax_Embeddings.e_range
                                                                    uu___29
                                                                    FStar_TypeChecker_NBETerm.e_range
                                                                    FStar_Reflection_V1_Builtins.range_of_sigelt in
                                                                    [uu___115] in
                                                                    uu___113
                                                                    ::
                                                                    uu___114 in
                                                                    uu___111
                                                                    ::
                                                                    uu___112 in
                                                                    uu___109
                                                                    ::
                                                                    uu___110 in
                                                                    uu___107
                                                                    ::
                                                                    uu___108 in
                                                                    uu___105
                                                                    ::
                                                                    uu___106 in
                                                                  uu___103 ::
                                                                    uu___104 in
                                                                uu___101 ::
                                                                  uu___102 in
                                                              uu___99 ::
                                                                uu___100 in
                                                            uu___97 ::
                                                              uu___98 in
                                                          uu___95 :: uu___96 in
                                                        uu___93 :: uu___94 in
                                                      uu___91 :: uu___92 in
                                                    uu___89 :: uu___90 in
                                                  uu___87 :: uu___88 in
                                                uu___85 :: uu___86 in
                                              uu___83 :: uu___84 in
                                            uu___81 :: uu___82 in
                                          uu___79 :: uu___80 in
                                        uu___77 :: uu___78 in
                                      uu___75 :: uu___76 in
                                    uu___73 :: uu___74 in
                                  uu___71 :: uu___72 in
                                uu___69 :: uu___70 in
                              uu___67 :: uu___68 in
                            uu___65 :: uu___66 in
                          uu___63 :: uu___64 in
                        uu___61 :: uu___62 in
                      uu___59 :: uu___60 in
                    uu___57 :: uu___58 in
                  uu___55 :: uu___56 in
                uu___53 :: uu___54 in
              uu___51 :: uu___52 in
            uu___49 :: uu___50 in
          uu___47 :: uu___48 in
        uu___45 :: uu___46 in
      uu___43 :: uu___44 in
    uu___41 :: uu___42 in
  uu___ :: uu___40
let (uu___40 : unit) =
  FStar_Compiler_List.iter FStar_TypeChecker_Cfg.register_extra_step
    reflection_primops