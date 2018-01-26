open Prims
let int1:
  'a 'b .
    FStar_Ident.lid ->
      ('a -> 'b) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'b FStar_Syntax_Embeddings.embedder ->
            FStar_Range.range ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ua  ->
        fun em  ->
          fun r  ->
            fun args  ->
              match args with
              | (a,uu____61)::[] ->
                  let uu____78 = ua a in
                  FStar_Util.bind_opt uu____78
                    (fun a1  ->
                       let uu____86 = let uu____87 = f a1 in em r uu____87 in
                       FStar_Pervasives_Native.Some uu____86)
              | uu____91 -> FStar_Pervasives_Native.None
let int2:
  'a 'b 'c .
    FStar_Ident.lid ->
      ('a -> 'b -> 'c) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'b FStar_Syntax_Embeddings.unembedder ->
            'c FStar_Syntax_Embeddings.embedder ->
              FStar_Range.range ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ua  ->
        fun ub  ->
          fun em  ->
            fun r  ->
              fun args  ->
                match args with
                | (a,uu____172)::(b,uu____174)::[] ->
                    let uu____201 = ua a in
                    FStar_Util.bind_opt uu____201
                      (fun a1  ->
                         let uu____209 = ub b in
                         FStar_Util.bind_opt uu____209
                           (fun b1  ->
                              let uu____217 =
                                let uu____218 = f a1 b1 in em r uu____218 in
                              FStar_Pervasives_Native.Some uu____217))
                | uu____222 -> FStar_Pervasives_Native.None
let reflection_primops: FStar_TypeChecker_Normalize.primitive_step Prims.list
  =
  let mklid nm = FStar_Reflection_Data.fstar_refl_basic_lid nm in
  let mk1 l arity fn =
    {
      FStar_TypeChecker_Normalize.name = l;
      FStar_TypeChecker_Normalize.arity = arity;
      FStar_TypeChecker_Normalize.strong_reduction_ok = false;
      FStar_TypeChecker_Normalize.requires_binder_substitution = false;
      FStar_TypeChecker_Normalize.interpretation =
        (fun ctxt  ->
           fun args  ->
             let uu____258 = FStar_TypeChecker_Normalize.psc_range ctxt in
             fn uu____258 args)
    } in
  let mk11 a b nm f u1 em =
    let l = mklid nm in mk1 l (Prims.parse_int "1") (int1 l f u1 em) in
  let mk2 a b c nm f u1 u2 em =
    let l = mklid nm in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em) in
  let uu____388 =
    mk11 () () "__inspect"
      (fun a412  -> (Obj.magic FStar_Reflection_Basic.inspect) a412)
      (Obj.magic FStar_Reflection_Basic.unembed_term)
      (Obj.magic FStar_Reflection_Basic.embed_term_view) in
  let uu____389 =
    let uu____392 =
      mk11 () () "__pack"
        (fun a413  -> (Obj.magic FStar_Reflection_Basic.pack) a413)
        (Obj.magic FStar_Reflection_Basic.unembed_term_view)
        (Obj.magic FStar_Reflection_Basic.embed_term) in
    let uu____393 =
      let uu____396 =
        mk11 () () "__inspect_fv"
          (fun a414  -> (Obj.magic FStar_Reflection_Basic.inspect_fv) a414)
          (Obj.magic FStar_Reflection_Basic.unembed_fvar)
          (Obj.magic FStar_Syntax_Embeddings.embed_string_list) in
      let uu____397 =
        let uu____400 =
          let uu____401 =
            FStar_Syntax_Embeddings.unembed_list
              FStar_Syntax_Embeddings.unembed_string in
          mk11 () () "__pack_fv"
            (fun a415  -> (Obj.magic FStar_Reflection_Basic.pack_fv) a415)
            (Obj.magic uu____401)
            (Obj.magic FStar_Reflection_Basic.embed_fvar) in
        let uu____410 =
          let uu____413 =
            mk11 () () "__inspect_comp"
              (fun a416  ->
                 (Obj.magic FStar_Reflection_Basic.inspect_comp) a416)
              (Obj.magic FStar_Reflection_Basic.unembed_comp)
              (Obj.magic FStar_Reflection_Basic.embed_comp_view) in
          let uu____414 =
            let uu____417 =
              mk11 () () "__pack_comp"
                (fun a417  ->
                   (Obj.magic FStar_Reflection_Basic.pack_comp) a417)
                (Obj.magic FStar_Reflection_Basic.unembed_comp_view)
                (Obj.magic FStar_Reflection_Basic.embed_comp) in
            let uu____418 =
              let uu____421 =
                mk11 () () "__inspect_bv"
                  (fun a418  ->
                     (Obj.magic FStar_Reflection_Basic.inspect_bv) a418)
                  (Obj.magic FStar_Reflection_Basic.unembed_binder)
                  (Obj.magic FStar_Syntax_Embeddings.embed_string) in
              let uu____422 =
                let uu____425 =
                  mk2 () () () "__compare_binder"
                    (fun a419  ->
                       fun a420  ->
                         (Obj.magic FStar_Reflection_Basic.compare_binder)
                           a419 a420)
                    (Obj.magic FStar_Reflection_Basic.unembed_binder)
                    (Obj.magic FStar_Reflection_Basic.unembed_binder)
                    (Obj.magic FStar_Reflection_Basic.embed_order) in
                let uu____426 =
                  let uu____429 =
                    mk11 () () "__type_of_binder"
                      (fun a421  ->
                         (Obj.magic FStar_Reflection_Basic.type_of_binder)
                           a421)
                      (Obj.magic FStar_Reflection_Basic.unembed_binder)
                      (Obj.magic FStar_Reflection_Basic.embed_term) in
                  let uu____430 =
                    let uu____433 =
                      mk2 () () () "__is_free"
                        (fun a422  ->
                           fun a423  ->
                             (Obj.magic FStar_Reflection_Basic.is_free) a422
                               a423)
                        (Obj.magic FStar_Reflection_Basic.unembed_binder)
                        (Obj.magic FStar_Reflection_Basic.unembed_term)
                        (Obj.magic FStar_Syntax_Embeddings.embed_bool) in
                    let uu____434 =
                      let uu____437 =
                        mk11 () () "__fresh_binder"
                          (fun a424  ->
                             (Obj.magic FStar_Reflection_Basic.fresh_binder)
                               a424)
                          (Obj.magic FStar_Reflection_Basic.unembed_term)
                          (Obj.magic FStar_Reflection_Basic.embed_binder) in
                      let uu____438 =
                        let uu____441 =
                          mk2 () () () "__term_eq"
                            (fun a425  ->
                               fun a426  ->
                                 (Obj.magic FStar_Reflection_Basic.term_eq)
                                   a425 a426)
                            (Obj.magic FStar_Reflection_Basic.unembed_term)
                            (Obj.magic FStar_Reflection_Basic.unembed_term)
                            (Obj.magic FStar_Syntax_Embeddings.embed_bool) in
                        let uu____442 =
                          let uu____445 =
                            mk11 () () "__term_to_string"
                              (fun a427  ->
                                 (Obj.magic
                                    FStar_Reflection_Basic.term_to_string)
                                   a427)
                              (Obj.magic FStar_Reflection_Basic.unembed_term)
                              (Obj.magic FStar_Syntax_Embeddings.embed_string) in
                          let uu____446 =
                            let uu____449 =
                              mk11 () () "__binders_of_env"
                                (fun a428  ->
                                   (Obj.magic
                                      FStar_Reflection_Basic.binders_of_env)
                                     a428)
                                (Obj.magic FStar_Reflection_Basic.unembed_env)
                                (Obj.magic
                                   FStar_Reflection_Basic.embed_binders) in
                            let uu____450 =
                              let uu____453 =
                                mk2 () () () "__lookup_typ"
                                  (fun a429  ->
                                     fun a430  ->
                                       (Obj.magic
                                          FStar_Reflection_Basic.lookup_typ)
                                         a429 a430)
                                  (Obj.magic
                                     FStar_Reflection_Basic.unembed_env)
                                  (Obj.magic
                                     FStar_Syntax_Embeddings.unembed_string_list)
                                  (Obj.magic
                                     FStar_Reflection_Basic.embed_sigelt_view) in
                              [uu____453] in
                            uu____449 :: uu____450 in
                          uu____445 :: uu____446 in
                        uu____441 :: uu____442 in
                      uu____437 :: uu____438 in
                    uu____433 :: uu____434 in
                  uu____429 :: uu____430 in
                uu____425 :: uu____426 in
              uu____421 :: uu____422 in
            uu____417 :: uu____418 in
          uu____413 :: uu____414 in
        uu____400 :: uu____410 in
      uu____396 :: uu____397 in
    uu____392 :: uu____393 in
  uu____388 :: uu____389