open Prims
let solve : 'a . 'a -> 'a = fun ev -> ev
let mk1 :
  'res 't1 .
    Prims.string ->
      't1 FStarC_Syntax_Embeddings_Base.embedding ->
        'res FStarC_Syntax_Embeddings_Base.embedding ->
          't1 FStarC_TypeChecker_NBETerm.embedding ->
            'res FStarC_TypeChecker_NBETerm.embedding ->
              ('t1 -> 'res) -> FStarC_TypeChecker_Primops_Base.primitive_step
  =
  fun nm ->
    fun uu___ ->
      fun uu___1 ->
        fun uu___2 ->
          fun uu___3 ->
            fun f ->
              let lid =
                FStarC_Reflection_V2_Constants.fstar_refl_builtins_lid nm in
              FStarC_TypeChecker_Primops_Base.mk1' Prims.int_zero lid uu___
                uu___2 uu___1 uu___3
                (fun x ->
                   let uu___4 = f x in FStar_Pervasives_Native.Some uu___4)
                (fun x ->
                   let uu___4 = f x in FStar_Pervasives_Native.Some uu___4)
let mk2 :
  'res 't1 't2 .
    Prims.string ->
      't1 FStarC_Syntax_Embeddings_Base.embedding ->
        't2 FStarC_Syntax_Embeddings_Base.embedding ->
          'res FStarC_Syntax_Embeddings_Base.embedding ->
            't1 FStarC_TypeChecker_NBETerm.embedding ->
              't2 FStarC_TypeChecker_NBETerm.embedding ->
                'res FStarC_TypeChecker_NBETerm.embedding ->
                  ('t1 -> 't2 -> 'res) ->
                    FStarC_TypeChecker_Primops_Base.primitive_step
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
                    FStarC_Reflection_V2_Constants.fstar_refl_builtins_lid nm in
                  FStarC_TypeChecker_Primops_Base.mk2' Prims.int_zero lid
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
      't1 FStarC_Syntax_Embeddings_Base.embedding ->
        't2 FStarC_Syntax_Embeddings_Base.embedding ->
          't3 FStarC_Syntax_Embeddings_Base.embedding ->
            'res FStarC_Syntax_Embeddings_Base.embedding ->
              't1 FStarC_TypeChecker_NBETerm.embedding ->
                't2 FStarC_TypeChecker_NBETerm.embedding ->
                  't3 FStarC_TypeChecker_NBETerm.embedding ->
                    'res FStarC_TypeChecker_NBETerm.embedding ->
                      ('t1 -> 't2 -> 't3 -> 'res) ->
                        FStarC_TypeChecker_Primops_Base.primitive_step
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
                        FStarC_Reflection_V2_Constants.fstar_refl_builtins_lid
                          nm in
                      FStarC_TypeChecker_Primops_Base.mk3' Prims.int_zero lid
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
let (reflection_primops :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    mk1 "inspect_ln" FStarC_Reflection_V2_Embeddings.e_term
      FStarC_Reflection_V2_Embeddings.e_term_view
      FStarC_Reflection_V2_NBEEmbeddings.e_term
      FStarC_Reflection_V2_NBEEmbeddings.e_term_view
      FStarC_Reflection_V2_Builtins.inspect_ln in
  let uu___1 =
    let uu___2 =
      mk1 "pack_ln" FStarC_Reflection_V2_Embeddings.e_term_view
        FStarC_Reflection_V2_Embeddings.e_term
        FStarC_Reflection_V2_NBEEmbeddings.e_term_view
        FStarC_Reflection_V2_NBEEmbeddings.e_term
        FStarC_Reflection_V2_Builtins.pack_ln in
    let uu___3 =
      let uu___4 =
        mk1 "inspect_fv" FStarC_Reflection_V2_Embeddings.e_fv
          FStarC_Syntax_Embeddings.e_string_list
          FStarC_Reflection_V2_NBEEmbeddings.e_fv
          FStarC_TypeChecker_NBETerm.e_string_list
          FStarC_Reflection_V2_Builtins.inspect_fv in
      let uu___5 =
        let uu___6 =
          mk1 "pack_fv" FStarC_Syntax_Embeddings.e_string_list
            FStarC_Reflection_V2_Embeddings.e_fv
            FStarC_TypeChecker_NBETerm.e_string_list
            FStarC_Reflection_V2_NBEEmbeddings.e_fv
            FStarC_Reflection_V2_Builtins.pack_fv in
        let uu___7 =
          let uu___8 =
            mk1 "inspect_comp" FStarC_Reflection_V2_Embeddings.e_comp
              FStarC_Reflection_V2_Embeddings.e_comp_view
              FStarC_Reflection_V2_NBEEmbeddings.e_comp
              FStarC_Reflection_V2_NBEEmbeddings.e_comp_view
              FStarC_Reflection_V2_Builtins.inspect_comp in
          let uu___9 =
            let uu___10 =
              mk1 "pack_comp" FStarC_Reflection_V2_Embeddings.e_comp_view
                FStarC_Reflection_V2_Embeddings.e_comp
                FStarC_Reflection_V2_NBEEmbeddings.e_comp_view
                FStarC_Reflection_V2_NBEEmbeddings.e_comp
                FStarC_Reflection_V2_Builtins.pack_comp in
            let uu___11 =
              let uu___12 =
                mk1 "inspect_universe"
                  FStarC_Reflection_V2_Embeddings.e_universe
                  FStarC_Reflection_V2_Embeddings.e_universe_view
                  FStarC_Reflection_V2_NBEEmbeddings.e_universe
                  FStarC_Reflection_V2_NBEEmbeddings.e_universe_view
                  FStarC_Reflection_V2_Builtins.inspect_universe in
              let uu___13 =
                let uu___14 =
                  mk1 "pack_universe"
                    FStarC_Reflection_V2_Embeddings.e_universe_view
                    FStarC_Reflection_V2_Embeddings.e_universe
                    FStarC_Reflection_V2_NBEEmbeddings.e_universe_view
                    FStarC_Reflection_V2_NBEEmbeddings.e_universe
                    FStarC_Reflection_V2_Builtins.pack_universe in
                let uu___15 =
                  let uu___16 =
                    mk1 "inspect_sigelt"
                      FStarC_Reflection_V2_Embeddings.e_sigelt
                      FStarC_Reflection_V2_Embeddings.e_sigelt_view
                      FStarC_Reflection_V2_NBEEmbeddings.e_sigelt
                      FStarC_Reflection_V2_NBEEmbeddings.e_sigelt_view
                      FStarC_Reflection_V2_Builtins.inspect_sigelt in
                  let uu___17 =
                    let uu___18 =
                      mk1 "pack_sigelt"
                        FStarC_Reflection_V2_Embeddings.e_sigelt_view
                        FStarC_Reflection_V2_Embeddings.e_sigelt
                        FStarC_Reflection_V2_NBEEmbeddings.e_sigelt_view
                        FStarC_Reflection_V2_NBEEmbeddings.e_sigelt
                        FStarC_Reflection_V2_Builtins.pack_sigelt in
                    let uu___19 =
                      let uu___20 =
                        mk1 "inspect_lb"
                          FStarC_Reflection_V2_Embeddings.e_letbinding
                          FStarC_Reflection_V2_Embeddings.e_lb_view
                          FStarC_Reflection_V2_NBEEmbeddings.e_letbinding
                          FStarC_Reflection_V2_NBEEmbeddings.e_lb_view
                          FStarC_Reflection_V2_Builtins.inspect_lb in
                      let uu___21 =
                        let uu___22 =
                          mk1 "pack_lb"
                            FStarC_Reflection_V2_Embeddings.e_lb_view
                            FStarC_Reflection_V2_Embeddings.e_letbinding
                            FStarC_Reflection_V2_NBEEmbeddings.e_lb_view
                            FStarC_Reflection_V2_NBEEmbeddings.e_letbinding
                            FStarC_Reflection_V2_Builtins.pack_lb in
                        let uu___23 =
                          let uu___24 =
                            mk1 "inspect_namedv"
                              FStarC_Reflection_V2_Embeddings.e_namedv
                              FStarC_Reflection_V2_Embeddings.e_namedv_view
                              FStarC_Reflection_V2_NBEEmbeddings.e_namedv
                              FStarC_Reflection_V2_NBEEmbeddings.e_namedv_view
                              FStarC_Reflection_V2_Builtins.inspect_namedv in
                          let uu___25 =
                            let uu___26 =
                              mk1 "pack_namedv"
                                FStarC_Reflection_V2_Embeddings.e_namedv_view
                                FStarC_Reflection_V2_Embeddings.e_namedv
                                FStarC_Reflection_V2_NBEEmbeddings.e_namedv_view
                                FStarC_Reflection_V2_NBEEmbeddings.e_namedv
                                FStarC_Reflection_V2_Builtins.pack_namedv in
                            let uu___27 =
                              let uu___28 =
                                mk1 "inspect_bv"
                                  FStarC_Reflection_V2_Embeddings.e_bv
                                  FStarC_Reflection_V2_Embeddings.e_bv_view
                                  FStarC_Reflection_V2_NBEEmbeddings.e_bv
                                  FStarC_Reflection_V2_NBEEmbeddings.e_bv_view
                                  FStarC_Reflection_V2_Builtins.inspect_bv in
                              let uu___29 =
                                let uu___30 =
                                  mk1 "pack_bv"
                                    FStarC_Reflection_V2_Embeddings.e_bv_view
                                    FStarC_Reflection_V2_Embeddings.e_bv
                                    FStarC_Reflection_V2_NBEEmbeddings.e_bv_view
                                    FStarC_Reflection_V2_NBEEmbeddings.e_bv
                                    FStarC_Reflection_V2_Builtins.pack_bv in
                                let uu___31 =
                                  let uu___32 =
                                    mk1 "inspect_binder"
                                      FStarC_Reflection_V2_Embeddings.e_binder
                                      FStarC_Reflection_V2_Embeddings.e_binder_view
                                      FStarC_Reflection_V2_NBEEmbeddings.e_binder
                                      FStarC_Reflection_V2_NBEEmbeddings.e_binder_view
                                      FStarC_Reflection_V2_Builtins.inspect_binder in
                                  let uu___33 =
                                    let uu___34 =
                                      mk1 "pack_binder"
                                        FStarC_Reflection_V2_Embeddings.e_binder_view
                                        FStarC_Reflection_V2_Embeddings.e_binder
                                        FStarC_Reflection_V2_NBEEmbeddings.e_binder_view
                                        FStarC_Reflection_V2_NBEEmbeddings.e_binder
                                        FStarC_Reflection_V2_Builtins.pack_binder in
                                    let uu___35 =
                                      let uu___36 =
                                        mk1 "sigelt_opts"
                                          FStarC_Reflection_V2_Embeddings.e_sigelt
                                          (FStarC_Syntax_Embeddings.e_option
                                             FStarC_Syntax_Embeddings.e_vconfig)
                                          FStarC_Reflection_V2_NBEEmbeddings.e_sigelt
                                          (FStarC_TypeChecker_NBETerm.e_option
                                             FStarC_TypeChecker_NBETerm.e_vconfig)
                                          FStarC_Reflection_V2_Builtins.sigelt_opts in
                                      let uu___37 =
                                        let uu___38 =
                                          mk1 "embed_vconfig"
                                            FStarC_Syntax_Embeddings.e_vconfig
                                            FStarC_Reflection_V2_Embeddings.e_term
                                            FStarC_TypeChecker_NBETerm.e_vconfig
                                            FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                            FStarC_Reflection_V2_Builtins.embed_vconfig in
                                        let uu___39 =
                                          let uu___40 =
                                            mk1 "sigelt_attrs"
                                              FStarC_Reflection_V2_Embeddings.e_sigelt
                                              (FStarC_Syntax_Embeddings.e_list
                                                 FStarC_Reflection_V2_Embeddings.e_term)
                                              FStarC_Reflection_V2_NBEEmbeddings.e_sigelt
                                              FStarC_Reflection_V2_NBEEmbeddings.e_attributes
                                              FStarC_Reflection_V2_Builtins.sigelt_attrs in
                                          let uu___41 =
                                            let uu___42 =
                                              mk2 "set_sigelt_attrs"
                                                (FStarC_Syntax_Embeddings.e_list
                                                   FStarC_Reflection_V2_Embeddings.e_term)
                                                FStarC_Reflection_V2_Embeddings.e_sigelt
                                                FStarC_Reflection_V2_Embeddings.e_sigelt
                                                FStarC_Reflection_V2_NBEEmbeddings.e_attributes
                                                FStarC_Reflection_V2_NBEEmbeddings.e_sigelt
                                                FStarC_Reflection_V2_NBEEmbeddings.e_sigelt
                                                FStarC_Reflection_V2_Builtins.set_sigelt_attrs in
                                            let uu___43 =
                                              let uu___44 =
                                                mk1 "sigelt_quals"
                                                  FStarC_Reflection_V2_Embeddings.e_sigelt
                                                  (FStarC_Syntax_Embeddings.e_list
                                                     FStarC_Reflection_V2_Embeddings.e_qualifier)
                                                  FStarC_Reflection_V2_NBEEmbeddings.e_sigelt
                                                  FStarC_Reflection_V2_NBEEmbeddings.e_qualifiers
                                                  FStarC_Reflection_V2_Builtins.sigelt_quals in
                                              let uu___45 =
                                                let uu___46 =
                                                  mk2 "set_sigelt_quals"
                                                    (FStarC_Syntax_Embeddings.e_list
                                                       FStarC_Reflection_V2_Embeddings.e_qualifier)
                                                    FStarC_Reflection_V2_Embeddings.e_sigelt
                                                    FStarC_Reflection_V2_Embeddings.e_sigelt
                                                    FStarC_Reflection_V2_NBEEmbeddings.e_qualifiers
                                                    FStarC_Reflection_V2_NBEEmbeddings.e_sigelt
                                                    FStarC_Reflection_V2_NBEEmbeddings.e_sigelt
                                                    FStarC_Reflection_V2_Builtins.set_sigelt_quals in
                                                let uu___47 =
                                                  let uu___48 =
                                                    mk2 "subst_term"
                                                      (FStarC_Syntax_Embeddings.e_list
                                                         FStarC_Reflection_V2_Embeddings.e_subst_elt)
                                                      FStarC_Reflection_V2_Embeddings.e_term
                                                      FStarC_Reflection_V2_Embeddings.e_term
                                                      FStarC_Reflection_V2_NBEEmbeddings.e_subst
                                                      FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                      FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                      FStarC_Reflection_V2_Builtins.subst_term in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      mk2 "subst_comp"
                                                        (FStarC_Syntax_Embeddings.e_list
                                                           FStarC_Reflection_V2_Embeddings.e_subst_elt)
                                                        FStarC_Reflection_V2_Embeddings.e_comp
                                                        FStarC_Reflection_V2_Embeddings.e_comp
                                                        FStarC_Reflection_V2_NBEEmbeddings.e_subst
                                                        FStarC_Reflection_V2_NBEEmbeddings.e_comp
                                                        FStarC_Reflection_V2_NBEEmbeddings.e_comp
                                                        FStarC_Reflection_V2_Builtins.subst_comp in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        mk2 "compare_bv"
                                                          FStarC_Reflection_V2_Embeddings.e_bv
                                                          FStarC_Reflection_V2_Embeddings.e_bv
                                                          FStarC_Syntax_Embeddings.e_order
                                                          FStarC_Reflection_V2_NBEEmbeddings.e_bv
                                                          FStarC_Reflection_V2_NBEEmbeddings.e_bv
                                                          FStarC_TypeChecker_NBETerm.e_order
                                                          FStarC_Reflection_V2_Builtins.compare_bv in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          mk2
                                                            "compare_namedv"
                                                            FStarC_Reflection_V2_Embeddings.e_namedv
                                                            FStarC_Reflection_V2_Embeddings.e_namedv
                                                            FStarC_Syntax_Embeddings.e_order
                                                            FStarC_Reflection_V2_NBEEmbeddings.e_namedv
                                                            FStarC_Reflection_V2_NBEEmbeddings.e_namedv
                                                            FStarC_TypeChecker_NBETerm.e_order
                                                            FStarC_Reflection_V2_Builtins.compare_namedv in
                                                        let uu___55 =
                                                          let uu___56 =
                                                            mk2
                                                              "lookup_attr_ses"
                                                              FStarC_Reflection_V2_Embeddings.e_term
                                                              FStarC_Reflection_V2_Embeddings.e_env
                                                              (FStarC_Syntax_Embeddings.e_list
                                                                 FStarC_Reflection_V2_Embeddings.e_sigelt)
                                                              FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                              FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                              (FStarC_TypeChecker_NBETerm.e_list
                                                                 FStarC_Reflection_V2_NBEEmbeddings.e_sigelt)
                                                              FStarC_Reflection_V2_Builtins.lookup_attr_ses in
                                                          let uu___57 =
                                                            let uu___58 =
                                                              mk2
                                                                "lookup_attr"
                                                                FStarC_Reflection_V2_Embeddings.e_term
                                                                FStarC_Reflection_V2_Embeddings.e_env
                                                                (FStarC_Syntax_Embeddings.e_list
                                                                   FStarC_Reflection_V2_Embeddings.e_fv)
                                                                FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                (FStarC_TypeChecker_NBETerm.e_list
                                                                   FStarC_Reflection_V2_NBEEmbeddings.e_fv)
                                                                FStarC_Reflection_V2_Builtins.lookup_attr in
                                                            let uu___59 =
                                                              let uu___60 =
                                                                mk1
                                                                  "all_defs_in_env"
                                                                  FStarC_Reflection_V2_Embeddings.e_env
                                                                  (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Reflection_V2_Embeddings.e_fv)
                                                                  FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                  (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_fv)
                                                                  FStarC_Reflection_V2_Builtins.all_defs_in_env in
                                                              let uu___61 =
                                                                let uu___62 =
                                                                  mk2
                                                                    "defs_in_module"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Syntax_Embeddings.e_string_list
                                                                    (
                                                                    FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Reflection_V2_Embeddings.e_fv)
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_TypeChecker_NBETerm.e_string_list
                                                                    (
                                                                    FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_fv)
                                                                    FStarC_Reflection_V2_Builtins.defs_in_module in
                                                                let uu___63 =
                                                                  let uu___64
                                                                    =
                                                                    mk2
                                                                    "term_eq"
                                                                    FStarC_Reflection_V2_Embeddings.e_term
                                                                    FStarC_Reflection_V2_Embeddings.e_term
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Reflection_V2_Builtins.term_eq in
                                                                  let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    mk1
                                                                    "moduleof"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Syntax_Embeddings.e_string_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_TypeChecker_NBETerm.e_string_list
                                                                    FStarC_Reflection_V2_Builtins.moduleof in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    mk1
                                                                    "vars_of_env"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Reflection_V2_Embeddings.e_binding)
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_binding)
                                                                    FStarC_Reflection_V2_Builtins.vars_of_env in
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    mk2
                                                                    "lookup_typ"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Syntax_Embeddings.e_string_list
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    FStarC_Reflection_V2_Embeddings.e_sigelt)
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_TypeChecker_NBETerm.e_string_list
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_sigelt)
                                                                    FStarC_Reflection_V2_Builtins.lookup_typ in
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    mk1
                                                                    "env_open_modules"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_string_list)
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_string_list)
                                                                    FStarC_Reflection_V2_Builtins.env_open_modules in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    mk1
                                                                    "implode_qn"
                                                                    FStarC_Syntax_Embeddings.e_string_list
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_string_list
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_Reflection_V2_Builtins.implode_qn in
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    mk1
                                                                    "explode_qn"
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_string_list
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_string_list
                                                                    FStarC_Reflection_V2_Builtins.explode_qn in
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
                                                                    =
                                                                    mk2
                                                                    "compare_string"
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_int
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_int
                                                                    FStarC_Reflection_V2_Builtins.compare_string in
                                                                    let uu___79
                                                                    =
                                                                    let uu___80
                                                                    =
                                                                    mk2
                                                                    "push_namedv"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Reflection_V2_Embeddings.e_namedv
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_namedv
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_Builtins.push_namedv in
                                                                    let uu___81
                                                                    =
                                                                    let uu___82
                                                                    =
                                                                    mk1
                                                                    "range_of_term"
                                                                    FStarC_Reflection_V2_Embeddings.e_term
                                                                    FStarC_Syntax_Embeddings.e_range
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_range
                                                                    FStarC_Reflection_V2_Builtins.range_of_term in
                                                                    let uu___83
                                                                    =
                                                                    let uu___84
                                                                    =
                                                                    mk1
                                                                    "range_of_sigelt"
                                                                    FStarC_Reflection_V2_Embeddings.e_sigelt
                                                                    FStarC_Syntax_Embeddings.e_range
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_sigelt
                                                                    FStarC_TypeChecker_NBETerm.e_range
                                                                    FStarC_Reflection_V2_Builtins.range_of_sigelt in
                                                                    let uu___85
                                                                    =
                                                                    let uu___86
                                                                    =
                                                                    mk1
                                                                    "inspect_ident"
                                                                    FStarC_Reflection_V2_Embeddings.e_univ_name
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_range)
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_univ_name
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_range)
                                                                    FStarC_Reflection_V2_Builtins.inspect_ident in
                                                                    let uu___87
                                                                    =
                                                                    let uu___88
                                                                    =
                                                                    mk1
                                                                    "pack_ident"
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_range)
                                                                    FStarC_Reflection_V2_Embeddings.e_univ_name
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_range)
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_univ_name
                                                                    FStarC_Reflection_V2_Builtins.pack_ident in
                                                                    [uu___88] in
                                                                    uu___86
                                                                    ::
                                                                    uu___87 in
                                                                    uu___84
                                                                    ::
                                                                    uu___85 in
                                                                    uu___82
                                                                    ::
                                                                    uu___83 in
                                                                    uu___80
                                                                    ::
                                                                    uu___81 in
                                                                    uu___78
                                                                    ::
                                                                    uu___79 in
                                                                    uu___76
                                                                    ::
                                                                    uu___77 in
                                                                    uu___74
                                                                    ::
                                                                    uu___75 in
                                                                    uu___72
                                                                    ::
                                                                    uu___73 in
                                                                    uu___70
                                                                    ::
                                                                    uu___71 in
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
let (uu___0 : unit) =
  FStar_List.iter FStarC_TypeChecker_Cfg.register_extra_step
    reflection_primops