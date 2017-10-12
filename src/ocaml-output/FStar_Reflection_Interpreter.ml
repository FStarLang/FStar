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
              | (a,uu____69)::[] ->
                  let uu____86 = ua a in
                  FStar_Util.bind_opt uu____86
                    (fun a1  ->
                       let uu____94 = let uu____95 = f a1 in em r uu____95 in
                       FStar_Pervasives_Native.Some uu____94)
              | uu____99 -> FStar_Pervasives_Native.None
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
                | (a,uu____190)::(b,uu____192)::[] ->
                    let uu____219 = ua a in
                    FStar_Util.bind_opt uu____219
                      (fun a1  ->
                         let uu____227 = ub b in
                         FStar_Util.bind_opt uu____227
                           (fun b1  ->
                              let uu____235 =
                                let uu____236 = f a1 b1 in em r uu____236 in
                              FStar_Pervasives_Native.Some uu____235))
                | uu____240 -> FStar_Pervasives_Native.None
let reflection_primops: FStar_TypeChecker_Normalize.primitive_step Prims.list
  =
  let mklid nm = FStar_Reflection_Data.fstar_refl_basic_lid nm in
  let mk1 l arity fn =
    {
      FStar_TypeChecker_Normalize.name = l;
      FStar_TypeChecker_Normalize.arity = arity;
      FStar_TypeChecker_Normalize.strong_reduction_ok = false;
      FStar_TypeChecker_Normalize.interpretation = fn
    } in
  let mk11 nm f u1 em =
    let l = mklid nm in mk1 l (Prims.parse_int "1") (int1 l f u1 em) in
  let mk2 nm f u1 u2 em =
    let l = mklid nm in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em) in
  let uu____413 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view in
  let uu____414 =
    let uu____417 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        FStar_Reflection_Basic.embed_term in
    let uu____418 =
      let uu____421 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          FStar_Syntax_Embeddings.embed_string_list in
      let uu____424 =
        let uu____427 =
          let uu____428 =
            FStar_Syntax_Embeddings.unembed_list
              FStar_Syntax_Embeddings.unembed_string in
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv uu____428
            FStar_Reflection_Basic.embed_fvar in
        let uu____439 =
          let uu____442 =
            mk11 "__inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Basic.unembed_comp
              FStar_Reflection_Basic.embed_comp_view in
          let uu____443 =
            let uu____446 =
              mk11 "__pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Basic.unembed_comp_view
                FStar_Reflection_Basic.embed_comp in
            let uu____447 =
              let uu____450 =
                mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Syntax_Embeddings.embed_string in
              let uu____451 =
                let uu____454 =
                  mk2 "__compare_binder"
                    FStar_Reflection_Basic.compare_binder
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.embed_order in
                let uu____455 =
                  let uu____458 =
                    mk11 "__type_of_binder"
                      FStar_Reflection_Basic.type_of_binder
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_term in
                  let uu____465 =
                    let uu____468 =
                      mk2 "__is_free" FStar_Reflection_Basic.is_free
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Reflection_Basic.unembed_term
                        FStar_Syntax_Embeddings.embed_bool in
                    let uu____469 =
                      let uu____472 =
                        mk11 "__fresh_binder"
                          FStar_Reflection_Basic.fresh_binder
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_binder in
                      let uu____479 =
                        let uu____482 =
                          mk2 "__term_eq" FStar_Reflection_Basic.term_eq
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.unembed_term
                            FStar_Syntax_Embeddings.embed_bool in
                        let uu____483 =
                          let uu____486 =
                            mk11 "__term_to_string"
                              FStar_Reflection_Basic.term_to_string
                              FStar_Reflection_Basic.unembed_term
                              FStar_Syntax_Embeddings.embed_string in
                          let uu____487 =
                            let uu____490 =
                              mk11 "__binders_of_env"
                                FStar_Reflection_Basic.binders_of_env
                                FStar_Reflection_Basic.unembed_env
                                FStar_Reflection_Basic.embed_binders in
                            let uu____491 =
                              let uu____494 =
                                mk2 "__lookup_typ"
                                  FStar_Reflection_Basic.lookup_typ
                                  FStar_Reflection_Basic.unembed_env
                                  FStar_Syntax_Embeddings.unembed_string_list
                                  FStar_Reflection_Basic.embed_sigelt_view in
                              [uu____494] in
                            uu____490 :: uu____491 in
                          uu____486 :: uu____487 in
                        uu____482 :: uu____483 in
                      uu____472 :: uu____479 in
                    uu____468 :: uu____469 in
                  uu____458 :: uu____465 in
                uu____454 :: uu____455 in
              uu____450 :: uu____451 in
            uu____446 :: uu____447 in
          uu____442 :: uu____443 in
        uu____427 :: uu____439 in
      uu____421 :: uu____424 in
    uu____417 :: uu____418 in
  uu____413 :: uu____414