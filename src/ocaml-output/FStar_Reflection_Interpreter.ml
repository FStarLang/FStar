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
  let mk11 nm f u1 em =
    let l = mklid nm in mk1 l (Prims.parse_int "1") (int1 l f u1 em) in
  let mk2 nm f u1 u2 em =
    let l = mklid nm in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em) in
  let uu____401 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view in
  let uu____402 =
    let uu____405 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        FStar_Reflection_Basic.embed_term in
    let uu____406 =
      let uu____409 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          FStar_Syntax_Embeddings.embed_string_list in
      let uu____412 =
        let uu____415 =
          let uu____416 =
            FStar_Syntax_Embeddings.unembed_list
              FStar_Syntax_Embeddings.unembed_string in
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv uu____416
            FStar_Reflection_Basic.embed_fvar in
        let uu____427 =
          let uu____430 =
            mk11 "__inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Basic.unembed_comp
              FStar_Reflection_Basic.embed_comp_view in
          let uu____431 =
            let uu____434 =
              mk11 "__pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Basic.unembed_comp_view
                FStar_Reflection_Basic.embed_comp in
            let uu____435 =
              let uu____438 =
                mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Syntax_Embeddings.embed_string in
              let uu____439 =
                let uu____442 =
                  mk2 "__compare_binder"
                    FStar_Reflection_Basic.compare_binder
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.embed_order in
                let uu____443 =
                  let uu____446 =
                    mk11 "__type_of_binder"
                      FStar_Reflection_Basic.type_of_binder
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_term in
                  let uu____453 =
                    let uu____456 =
                      mk2 "__is_free" FStar_Reflection_Basic.is_free
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Reflection_Basic.unembed_term
                        FStar_Syntax_Embeddings.embed_bool in
                    let uu____457 =
                      let uu____460 =
                        mk11 "__fresh_binder"
                          FStar_Reflection_Basic.fresh_binder
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_binder in
                      let uu____467 =
                        let uu____470 =
                          mk2 "__term_eq" FStar_Reflection_Basic.term_eq
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.unembed_term
                            FStar_Syntax_Embeddings.embed_bool in
                        let uu____471 =
                          let uu____474 =
                            mk11 "__term_to_string"
                              FStar_Reflection_Basic.term_to_string
                              FStar_Reflection_Basic.unembed_term
                              FStar_Syntax_Embeddings.embed_string in
                          let uu____475 =
                            let uu____478 =
                              mk11 "__binders_of_env"
                                FStar_Reflection_Basic.binders_of_env
                                FStar_Reflection_Basic.unembed_env
                                FStar_Reflection_Basic.embed_binders in
                            let uu____479 =
                              let uu____482 =
                                mk2 "__lookup_typ"
                                  FStar_Reflection_Basic.lookup_typ
                                  FStar_Reflection_Basic.unembed_env
                                  FStar_Syntax_Embeddings.unembed_string_list
                                  FStar_Reflection_Basic.embed_sigelt_view in
                              [uu____482] in
                            uu____478 :: uu____479 in
                          uu____474 :: uu____475 in
                        uu____470 :: uu____471 in
                      uu____460 :: uu____467 in
                    uu____456 :: uu____457 in
                  uu____446 :: uu____453 in
                uu____442 :: uu____443 in
              uu____438 :: uu____439 in
            uu____434 :: uu____435 in
          uu____430 :: uu____431 in
        uu____415 :: uu____427 in
      uu____409 :: uu____412 in
    uu____405 :: uu____406 in
  uu____401 :: uu____402