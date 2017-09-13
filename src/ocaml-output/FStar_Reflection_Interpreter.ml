open Prims
let int1:
  'a 'b .
    FStar_Ident.lid ->
      ('a -> 'b) ->
        (FStar_Syntax_Syntax.term -> 'a) ->
          ('b -> FStar_Syntax_Syntax.term) ->
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
                  let uu____78 =
                    let uu____79 = let uu____80 = ua a in f uu____80 in
                    em uu____79 in
                  FStar_Pervasives_Native.Some uu____78
              | uu____81 -> FStar_Pervasives_Native.None
let int2:
  'a 'b 'c .
    FStar_Ident.lid ->
      ('a -> 'b -> 'c) ->
        (FStar_Syntax_Syntax.term -> 'a) ->
          (FStar_Syntax_Syntax.term -> 'b) ->
            ('c -> FStar_Syntax_Syntax.term) ->
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
                | (a,uu____161)::(b,uu____163)::[] ->
                    let uu____190 =
                      let uu____191 =
                        let uu____192 = ua a in
                        let uu____193 = ub b in f uu____192 uu____193 in
                      em uu____191 in
                    FStar_Pervasives_Native.Some uu____190
                | uu____194 -> FStar_Pervasives_Native.None
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
  let uu____324 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view in
  let uu____325 =
    let uu____328 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        FStar_Reflection_Basic.embed_term in
    let uu____329 =
      let uu____332 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          FStar_Syntax_Embeddings.embed_string_list in
      let uu____335 =
        let uu____338 =
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv
            (FStar_Syntax_Embeddings.unembed_list
               FStar_Syntax_Embeddings.unembed_string)
            FStar_Reflection_Basic.embed_fvar in
        let uu____341 =
          let uu____344 =
            mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
              FStar_Reflection_Basic.unembed_binder
              FStar_Syntax_Embeddings.embed_string in
          let uu____345 =
            let uu____348 =
              mk2 "__compare_binder" FStar_Reflection_Basic.compare_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.embed_order in
            let uu____349 =
              let uu____352 =
                mk11 "__type_of_binder" FStar_Reflection_Basic.type_of_binder
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Reflection_Basic.embed_term in
              let uu____359 =
                let uu____362 =
                  mk2 "__is_free" FStar_Reflection_Basic.is_free
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.unembed_term
                    FStar_Syntax_Embeddings.embed_bool in
                let uu____363 =
                  let uu____366 =
                    mk11 "__fresh_binder" FStar_Reflection_Basic.fresh_binder
                      FStar_Reflection_Basic.unembed_term
                      FStar_Reflection_Basic.embed_binder in
                  let uu____373 =
                    let uu____376 =
                      mk2 "__term_eq" FStar_Reflection_Basic.term_eq
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.unembed_term
                        FStar_Syntax_Embeddings.embed_bool in
                    let uu____377 =
                      let uu____380 =
                        mk11 "__term_to_string"
                          FStar_Reflection_Basic.term_to_string
                          FStar_Reflection_Basic.unembed_term
                          FStar_Syntax_Embeddings.embed_string in
                      let uu____381 =
                        let uu____384 =
                          mk11 "__binders_of_env"
                            FStar_Reflection_Basic.binders_of_env
                            FStar_Reflection_Basic.unembed_env
                            FStar_Reflection_Basic.embed_binders in
                        let uu____385 =
                          let uu____388 =
                            mk2 "__lookup_typ"
                              FStar_Reflection_Basic.lookup_typ
                              FStar_Reflection_Basic.unembed_env
                              FStar_Syntax_Embeddings.unembed_string_list
                              FStar_Reflection_Basic.embed_sigelt_view in
                          [uu____388] in
                        uu____384 :: uu____385 in
                      uu____380 :: uu____381 in
                    uu____376 :: uu____377 in
                  uu____366 :: uu____373 in
                uu____362 :: uu____363 in
              uu____352 :: uu____359 in
            uu____348 :: uu____349 in
          uu____344 :: uu____345 in
        uu____338 :: uu____341 in
      uu____332 :: uu____335 in
    uu____328 :: uu____329 in
  uu____324 :: uu____325