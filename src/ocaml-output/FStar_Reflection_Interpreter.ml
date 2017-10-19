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
      FStar_TypeChecker_Normalize.requires_binder_substitution = false;
      FStar_TypeChecker_Normalize.interpretation =
        (fun ctxt  ->
           fun args  ->
             let uu____276 = FStar_TypeChecker_Normalize.psc_range ctxt in
             fn uu____276 args)
    } in
  let mk11 nm f u1 em =
    let l = mklid nm in mk1 l (Prims.parse_int "1") (int1 l f u1 em) in
  let mk2 nm f u1 u2 em =
    let l = mklid nm in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em) in
  let uu____419 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view in
  let uu____420 =
    let uu____423 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        FStar_Reflection_Basic.embed_term in
    let uu____424 =
      let uu____427 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          FStar_Syntax_Embeddings.embed_string_list in
      let uu____430 =
        let uu____433 =
          let uu____434 =
            FStar_Syntax_Embeddings.unembed_list
              FStar_Syntax_Embeddings.unembed_string in
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv uu____434
            FStar_Reflection_Basic.embed_fvar in
        let uu____445 =
          let uu____448 =
            mk11 "__inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Basic.unembed_comp
              FStar_Reflection_Basic.embed_comp_view in
          let uu____449 =
            let uu____452 =
              mk11 "__pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Basic.unembed_comp_view
                FStar_Reflection_Basic.embed_comp in
            let uu____453 =
              let uu____456 =
                mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Syntax_Embeddings.embed_string in
              let uu____457 =
                let uu____460 =
                  mk2 "__compare_binder"
                    FStar_Reflection_Basic.compare_binder
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.embed_order in
                let uu____461 =
                  let uu____464 =
                    mk11 "__type_of_binder"
                      FStar_Reflection_Basic.type_of_binder
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_term in
                  let uu____471 =
                    let uu____474 =
                      mk2 "__is_free" FStar_Reflection_Basic.is_free
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Reflection_Basic.unembed_term
                        FStar_Syntax_Embeddings.embed_bool in
                    let uu____475 =
                      let uu____478 =
                        mk11 "__fresh_binder"
                          FStar_Reflection_Basic.fresh_binder
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_binder in
                      let uu____485 =
                        let uu____488 =
                          mk2 "__term_eq" FStar_Reflection_Basic.term_eq
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.unembed_term
                            FStar_Syntax_Embeddings.embed_bool in
                        let uu____489 =
                          let uu____492 =
                            mk11 "__term_to_string"
                              FStar_Reflection_Basic.term_to_string
                              FStar_Reflection_Basic.unembed_term
                              FStar_Syntax_Embeddings.embed_string in
                          let uu____493 =
                            let uu____496 =
                              mk11 "__binders_of_env"
                                FStar_Reflection_Basic.binders_of_env
                                FStar_Reflection_Basic.unembed_env
                                FStar_Reflection_Basic.embed_binders in
                            let uu____497 =
                              let uu____500 =
                                mk2 "__lookup_typ"
                                  FStar_Reflection_Basic.lookup_typ
                                  FStar_Reflection_Basic.unembed_env
                                  FStar_Syntax_Embeddings.unembed_string_list
                                  FStar_Reflection_Basic.embed_sigelt_view in
                              [uu____500] in
                            uu____496 :: uu____497 in
                          uu____492 :: uu____493 in
                        uu____488 :: uu____489 in
                      uu____478 :: uu____485 in
                    uu____474 :: uu____475 in
                  uu____464 :: uu____471 in
                uu____460 :: uu____461 in
              uu____456 :: uu____457 in
            uu____452 :: uu____453 in
          uu____448 :: uu____449 in
        uu____433 :: uu____445 in
      uu____427 :: uu____430 in
    uu____423 :: uu____424 in
  uu____419 :: uu____420