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
      FStar_Compiler_Range.range ->
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
                    FStar_Compiler_Util.bind_opt uu___1
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
                      FStar_Compiler_Util.bind_opt uu___2
                        (fun a2 ->
                           let uu___3 = try_unembed eb b1 n in
                           FStar_Compiler_Util.bind_opt uu___3
                             (fun b2 ->
                                let uu___4 =
                                  let uu___5 =
                                    FStar_TypeChecker_Cfg.psc_range psc in
                                  let uu___6 = f a2 b2 in
                                  embed er uu___5 uu___6 n in
                                FStar_Pervasives_Native.Some uu___4))
                  | uu___ -> FStar_Pervasives_Native.None
let int3 :
  'a 'b 'c 'r .
    FStar_Ident.lid ->
      ('a -> 'b -> 'c -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'c FStar_Syntax_Embeddings.embedding ->
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
          fun ec ->
            fun er ->
              fun psc ->
                fun n ->
                  fun args ->
                    match args with
                    | (a1, uu___)::(b1, uu___1)::(c1, uu___2)::[] ->
                        let uu___3 = try_unembed ea a1 n in
                        FStar_Compiler_Util.bind_opt uu___3
                          (fun a2 ->
                             let uu___4 = try_unembed eb b1 n in
                             FStar_Compiler_Util.bind_opt uu___4
                               (fun b2 ->
                                  let uu___5 = try_unembed ec c1 n in
                                  FStar_Compiler_Util.bind_opt uu___5
                                    (fun c2 ->
                                       let uu___6 =
                                         let uu___7 =
                                           FStar_TypeChecker_Cfg.psc_range
                                             psc in
                                         let uu___8 = f a2 b2 c2 in
                                         embed er uu___7 uu___8 n in
                                       FStar_Pervasives_Native.Some uu___6)))
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
                  FStar_Compiler_Util.bind_opt uu___1
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
                    FStar_Compiler_Util.bind_opt uu___2
                      (fun a2 ->
                         let uu___3 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b1 in
                         FStar_Compiler_Util.bind_opt uu___3
                           (fun b2 ->
                              let uu___4 =
                                let uu___5 = f a2 b2 in
                                FStar_TypeChecker_NBETerm.embed er cb uu___5 in
                              FStar_Pervasives_Native.Some uu___4))
                | uu___ -> FStar_Pervasives_Native.None
let nbe_int3 :
  'a 'b 'c 'r .
    FStar_Ident.lid ->
      ('a -> 'b -> 'c -> 'r) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'b FStar_TypeChecker_NBETerm.embedding ->
            'c FStar_TypeChecker_NBETerm.embedding ->
              'r FStar_TypeChecker_NBETerm.embedding ->
                FStar_TypeChecker_NBETerm.nbe_cbs ->
                  FStar_TypeChecker_NBETerm.args ->
                    FStar_TypeChecker_NBETerm.t
                      FStar_Pervasives_Native.option
  =
  fun m ->
    fun f ->
      fun ea ->
        fun eb ->
          fun ec ->
            fun er ->
              fun cb ->
                fun args ->
                  match args with
                  | (a1, uu___)::(b1, uu___1)::(c1, uu___2)::[] ->
                      let uu___3 = FStar_TypeChecker_NBETerm.unembed ea cb a1 in
                      FStar_Compiler_Util.bind_opt uu___3
                        (fun a2 ->
                           let uu___4 =
                             FStar_TypeChecker_NBETerm.unembed eb cb b1 in
                           FStar_Compiler_Util.bind_opt uu___4
                             (fun b2 ->
                                let uu___5 =
                                  FStar_TypeChecker_NBETerm.unembed ec cb c1 in
                                FStar_Compiler_Util.bind_opt uu___5
                                  (fun c2 ->
                                     let uu___6 =
                                       let uu___7 = f a2 b2 c2 in
                                       FStar_TypeChecker_NBETerm.embed er cb
                                         uu___7 in
                                     FStar_Pervasives_Native.Some uu___6)))
                  | uu___ -> FStar_Pervasives_Native.None
let (mklid : Prims.string -> FStar_Ident.lid) =
  fun nm -> FStar_Reflection_Constants.fstar_refl_builtins_lid nm
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
            FStar_TypeChecker_Cfg.interpretation =
              (fun psc -> fun cbs -> fun _us -> fun args -> fn psc cbs args);
            FStar_TypeChecker_Cfg.interpretation_nbe =
              (fun cbs -> fun _us -> fun args -> nbe_fn cbs args)
          }
type 'a dualemb =
  ('a FStar_Syntax_Embeddings.embedding * 'a
    FStar_TypeChecker_NBETerm.embedding)
let (e_int : FStar_BigInt.t dualemb) =
  (FStar_Syntax_Embeddings.e_int, FStar_TypeChecker_NBETerm.e_int)
let (e_bool : Prims.bool dualemb) =
  (FStar_Syntax_Embeddings.e_bool, FStar_TypeChecker_NBETerm.e_bool)
let (e_string : Prims.string dualemb) =
  (FStar_Syntax_Embeddings.e_string, FStar_TypeChecker_NBETerm.e_string)
let (e_order : FStar_Order.order dualemb) =
  (FStar_Reflection_Embeddings.e_order,
    FStar_Reflection_NBEEmbeddings.e_order)
let (e_term : FStar_Syntax_Syntax.term dualemb) =
  (FStar_Reflection_Embeddings.e_term, FStar_Reflection_NBEEmbeddings.e_term)
let (e_term_view : FStar_Reflection_Data.term_view dualemb) =
  (FStar_Reflection_Embeddings.e_term_view,
    FStar_Reflection_NBEEmbeddings.e_term_view)
let (e_fv : FStar_Syntax_Syntax.fv dualemb) =
  (FStar_Reflection_Embeddings.e_fv, FStar_Reflection_NBEEmbeddings.e_fv)
let (e_bv : FStar_Syntax_Syntax.bv dualemb) =
  (FStar_Reflection_Embeddings.e_bv, FStar_Reflection_NBEEmbeddings.e_bv)
let (e_bv_view : FStar_Reflection_Data.bv_view dualemb) =
  (FStar_Reflection_Embeddings.e_bv_view,
    FStar_Reflection_NBEEmbeddings.e_bv_view)
let (e_comp : FStar_Syntax_Syntax.comp dualemb) =
  (FStar_Reflection_Embeddings.e_comp, FStar_Reflection_NBEEmbeddings.e_comp)
let (e_comp_view : FStar_Reflection_Data.comp_view dualemb) =
  (FStar_Reflection_Embeddings.e_comp_view,
    FStar_Reflection_NBEEmbeddings.e_comp_view)
let (e_universe : FStar_Syntax_Syntax.universe dualemb) =
  (FStar_Reflection_Embeddings.e_universe,
    FStar_Reflection_NBEEmbeddings.e_universe)
let (e_universe_view : FStar_Reflection_Data.universe_view dualemb) =
  (FStar_Reflection_Embeddings.e_universe_view,
    FStar_Reflection_NBEEmbeddings.e_universe_view)
let (e_sigelt : FStar_Syntax_Syntax.sigelt dualemb) =
  (FStar_Reflection_Embeddings.e_sigelt,
    FStar_Reflection_NBEEmbeddings.e_sigelt)
let (e_sigelt_view : FStar_Reflection_Data.sigelt_view dualemb) =
  (FStar_Reflection_Embeddings.e_sigelt_view,
    FStar_Reflection_NBEEmbeddings.e_sigelt_view)
let (e_binder : FStar_Syntax_Syntax.binder dualemb) =
  (FStar_Reflection_Embeddings.e_binder,
    FStar_Reflection_NBEEmbeddings.e_binder)
let (e_binder_view : FStar_Reflection_Data.binder_view dualemb) =
  (FStar_Reflection_Embeddings.e_binder_view,
    FStar_Reflection_NBEEmbeddings.e_binder_view)
let (e_binders : FStar_Syntax_Syntax.binders dualemb) =
  (FStar_Reflection_Embeddings.e_binders,
    FStar_Reflection_NBEEmbeddings.e_binders)
let (e_letbinding : FStar_Syntax_Syntax.letbinding dualemb) =
  (FStar_Reflection_Embeddings.e_letbinding,
    FStar_Reflection_NBEEmbeddings.e_letbinding)
let (e_lb_view : FStar_Reflection_Data.lb_view dualemb) =
  (FStar_Reflection_Embeddings.e_lb_view,
    FStar_Reflection_NBEEmbeddings.e_lb_view)
let (e_env : FStar_TypeChecker_Env.env dualemb) =
  (FStar_Reflection_Embeddings.e_env, FStar_Reflection_NBEEmbeddings.e_env)
let (e_aqualv : FStar_Reflection_Data.aqualv dualemb) =
  (FStar_Reflection_Embeddings.e_aqualv,
    FStar_Reflection_NBEEmbeddings.e_aqualv)
let (e_vconfig : FStar_VConfig.vconfig dualemb) =
  (FStar_Syntax_Embeddings.e_vconfig, FStar_TypeChecker_NBETerm.e_vconfig)
let (e_attributes : FStar_Syntax_Syntax.attribute Prims.list dualemb) =
  (FStar_Reflection_Embeddings.e_attributes,
    FStar_Reflection_NBEEmbeddings.e_attributes)
let (e_qualifiers : FStar_Reflection_Data.qualifiers dualemb) =
  (FStar_Reflection_Embeddings.e_qualifiers,
    FStar_Reflection_NBEEmbeddings.e_qualifiers)
let e_list : 'a . 'a dualemb -> 'a Prims.list dualemb =
  fun e ->
    let uu___ =
      FStar_Syntax_Embeddings.e_list (FStar_Pervasives_Native.fst e) in
    let uu___1 =
      FStar_TypeChecker_NBETerm.e_list (FStar_Pervasives_Native.snd e) in
    (uu___, uu___1)
let e_option : 'a . 'a dualemb -> 'a FStar_Pervasives_Native.option dualemb =
  fun e ->
    let uu___ =
      FStar_Syntax_Embeddings.e_option (FStar_Pervasives_Native.fst e) in
    let uu___1 =
      FStar_TypeChecker_NBETerm.e_option (FStar_Pervasives_Native.snd e) in
    (uu___, uu___1)
let (e_string_list : Prims.string Prims.list dualemb) = e_list e_string
let mk1 :
  'a 'r .
    Prims.string ->
      ('a -> 'r) ->
        'a dualemb -> 'r dualemb -> FStar_TypeChecker_Cfg.primitive_step
  =
  fun nm ->
    fun f ->
      fun ea ->
        fun er ->
          let l = mklid nm in
          mk l Prims.int_one
            (int1 l f (FStar_Pervasives_Native.fst ea)
               (FStar_Pervasives_Native.fst er))
            (nbe_int1 l f (FStar_Pervasives_Native.snd ea)
               (FStar_Pervasives_Native.snd er))
let mk2 :
  'a 'b 'r .
    Prims.string ->
      ('a -> 'b -> 'r) ->
        'a dualemb ->
          'b dualemb -> 'r dualemb -> FStar_TypeChecker_Cfg.primitive_step
  =
  fun nm ->
    fun f ->
      fun ea ->
        fun eb ->
          fun er ->
            let l = mklid nm in
            mk l (Prims.of_int (2))
              (int2 l f (FStar_Pervasives_Native.fst ea)
                 (FStar_Pervasives_Native.fst eb)
                 (FStar_Pervasives_Native.fst er))
              (nbe_int2 l f (FStar_Pervasives_Native.snd ea)
                 (FStar_Pervasives_Native.snd eb)
                 (FStar_Pervasives_Native.snd er))
let mk3 :
  'a 'b 'c 'r .
    Prims.string ->
      ('a -> 'b -> 'c -> 'r) ->
        'a dualemb ->
          'b dualemb ->
            'c dualemb -> 'r dualemb -> FStar_TypeChecker_Cfg.primitive_step
  =
  fun nm ->
    fun f ->
      fun ea ->
        fun eb ->
          fun ec ->
            fun er ->
              let l = mklid nm in
              mk l (Prims.of_int (3))
                (int3 l f (FStar_Pervasives_Native.fst ea)
                   (FStar_Pervasives_Native.fst eb)
                   (FStar_Pervasives_Native.fst ec)
                   (FStar_Pervasives_Native.fst er))
                (nbe_int3 l f (FStar_Pervasives_Native.snd ea)
                   (FStar_Pervasives_Native.snd eb)
                   (FStar_Pervasives_Native.snd ec)
                   (FStar_Pervasives_Native.snd er))
let (reflection_primops : FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  let uu___ =
    mk1 "inspect_ln" FStar_Reflection_Basic.inspect_ln e_term e_term_view in
  let uu___1 =
    let uu___2 =
      mk1 "pack_ln" FStar_Reflection_Basic.pack_ln e_term_view e_term in
    let uu___3 =
      let uu___4 =
        mk1 "inspect_fv" FStar_Reflection_Basic.inspect_fv e_fv e_string_list in
      let uu___5 =
        let uu___6 =
          mk1 "pack_fv" FStar_Reflection_Basic.pack_fv e_string_list e_fv in
        let uu___7 =
          let uu___8 =
            mk1 "inspect_comp" FStar_Reflection_Basic.inspect_comp e_comp
              e_comp_view in
          let uu___9 =
            let uu___10 =
              mk1 "pack_comp" FStar_Reflection_Basic.pack_comp e_comp_view
                e_comp in
            let uu___11 =
              let uu___12 =
                mk1 "inspect_universe"
                  FStar_Reflection_Basic.inspect_universe e_universe
                  e_universe_view in
              let uu___13 =
                let uu___14 =
                  mk1 "pack_universe" FStar_Reflection_Basic.pack_universe
                    e_universe_view e_universe in
                let uu___15 =
                  let uu___16 =
                    mk1 "inspect_sigelt"
                      FStar_Reflection_Basic.inspect_sigelt e_sigelt
                      e_sigelt_view in
                  let uu___17 =
                    let uu___18 =
                      mk1 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                        e_sigelt_view e_sigelt in
                    let uu___19 =
                      let uu___20 =
                        mk1 "inspect_lb" FStar_Reflection_Basic.inspect_lb
                          e_letbinding e_lb_view in
                      let uu___21 =
                        let uu___22 =
                          mk1 "pack_lb" FStar_Reflection_Basic.pack_lb
                            e_lb_view e_letbinding in
                        let uu___23 =
                          let uu___24 =
                            mk1 "inspect_bv"
                              FStar_Reflection_Basic.inspect_bv e_bv
                              e_bv_view in
                          let uu___25 =
                            let uu___26 =
                              mk2 "pack_bv" FStar_Reflection_Basic.pack_bv
                                e_string e_bv_view e_bv in
                            let uu___27 =
                              let uu___28 =
                                mk1 "inspect_binder"
                                  FStar_Reflection_Basic.inspect_binder
                                  e_binder e_binder_view in
                              let uu___29 =
                                let uu___30 =
                                  let uu___31 = e_list e_term in
                                  mk3 "pack_binder"
                                    FStar_Reflection_Basic.pack_binder e_bv
                                    e_aqualv uu___31 e_binder in
                                let uu___31 =
                                  let uu___32 =
                                    let uu___33 = e_option e_vconfig in
                                    mk1 "sigelt_opts"
                                      FStar_Reflection_Basic.sigelt_opts
                                      e_sigelt uu___33 in
                                  let uu___33 =
                                    let uu___34 =
                                      mk1 "embed_vconfig"
                                        FStar_Reflection_Basic.embed_vconfig
                                        e_vconfig e_term in
                                    let uu___35 =
                                      let uu___36 =
                                        mk1 "sigelt_attrs"
                                          FStar_Reflection_Basic.sigelt_attrs
                                          e_sigelt e_attributes in
                                      let uu___37 =
                                        let uu___38 =
                                          mk2 "set_sigelt_attrs"
                                            FStar_Reflection_Basic.set_sigelt_attrs
                                            e_attributes e_sigelt e_sigelt in
                                        let uu___39 =
                                          let uu___40 =
                                            mk1 "sigelt_quals"
                                              FStar_Reflection_Basic.sigelt_quals
                                              e_sigelt e_qualifiers in
                                          let uu___41 =
                                            let uu___42 =
                                              mk2 "set_sigelt_quals"
                                                FStar_Reflection_Basic.set_sigelt_quals
                                                e_qualifiers e_sigelt
                                                e_sigelt in
                                            let uu___43 =
                                              let uu___44 =
                                                mk3 "subst"
                                                  FStar_Reflection_Basic.subst
                                                  e_bv e_term e_term e_term in
                                              let uu___45 =
                                                let uu___46 =
                                                  mk2 "close_term"
                                                    FStar_Reflection_Basic.close_term
                                                    e_binder e_term e_term in
                                                let uu___47 =
                                                  let uu___48 =
                                                    mk2 "compare_bv"
                                                      FStar_Reflection_Basic.compare_bv
                                                      e_bv e_bv e_order in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      mk2 "is_free"
                                                        FStar_Reflection_Basic.is_free
                                                        e_bv e_term e_bool in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        let uu___53 =
                                                          e_list e_bv in
                                                        mk1 "free_bvs"
                                                          FStar_Reflection_Basic.free_bvs
                                                          e_term uu___53 in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          let uu___55 =
                                                            e_list e_int in
                                                          mk1 "free_uvars"
                                                            FStar_Reflection_Basic.free_uvars
                                                            e_term uu___55 in
                                                        let uu___55 =
                                                          let uu___56 =
                                                            let uu___57 =
                                                              e_list e_fv in
                                                            mk2 "lookup_attr"
                                                              FStar_Reflection_Basic.lookup_attr
                                                              e_term e_env
                                                              uu___57 in
                                                          let uu___57 =
                                                            let uu___58 =
                                                              let uu___59 =
                                                                e_list e_fv in
                                                              mk1
                                                                "all_defs_in_env"
                                                                FStar_Reflection_Basic.all_defs_in_env
                                                                e_env uu___59 in
                                                            let uu___59 =
                                                              let uu___60 =
                                                                let uu___61 =
                                                                  e_list e_fv in
                                                                mk2
                                                                  "defs_in_module"
                                                                  FStar_Reflection_Basic.defs_in_module
                                                                  e_env
                                                                  e_string_list
                                                                  uu___61 in
                                                              let uu___61 =
                                                                let uu___62 =
                                                                  mk2
                                                                    "term_eq"
                                                                    FStar_Reflection_Basic.term_eq
                                                                    e_term
                                                                    e_term
                                                                    e_bool in
                                                                let uu___63 =
                                                                  let uu___64
                                                                    =
                                                                    mk1
                                                                    "moduleof"
                                                                    FStar_Reflection_Basic.moduleof
                                                                    e_env
                                                                    e_string_list in
                                                                  let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    mk1
                                                                    "binders_of_env"
                                                                    FStar_Reflection_Basic.binders_of_env
                                                                    e_env
                                                                    e_binders in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    let uu___69
                                                                    =
                                                                    e_option
                                                                    e_sigelt in
                                                                    mk2
                                                                    "lookup_typ"
                                                                    FStar_Reflection_Basic.lookup_typ
                                                                    e_env
                                                                    e_string_list
                                                                    uu___69 in
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    let uu___71
                                                                    =
                                                                    e_list
                                                                    e_string_list in
                                                                    mk1
                                                                    "env_open_modules"
                                                                    FStar_Reflection_Basic.env_open_modules
                                                                    e_env
                                                                    uu___71 in
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    mk1
                                                                    "implode_qn"
                                                                    FStar_Reflection_Basic.implode_qn
                                                                    e_string_list
                                                                    e_string in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    mk1
                                                                    "explode_qn"
                                                                    FStar_Reflection_Basic.explode_qn
                                                                    e_string
                                                                    e_string_list in
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    mk2
                                                                    "compare_string"
                                                                    FStar_Reflection_Basic.compare_string
                                                                    e_string
                                                                    e_string
                                                                    e_int in
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
                                                                    =
                                                                    mk2
                                                                    "push_binder"
                                                                    FStar_Reflection_Basic.push_binder
                                                                    e_env
                                                                    e_binder
                                                                    e_env in
                                                                    [uu___78] in
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
let (uu___200 : unit) =
  FStar_Compiler_List.iter FStar_TypeChecker_Cfg.register_extra_step
    reflection_primops