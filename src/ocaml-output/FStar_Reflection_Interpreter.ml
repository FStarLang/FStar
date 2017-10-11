open Prims
let int1:
  'a 'b .
    FStar_Ident.lid ->
      ('a -> 'b) ->
        (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
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
              | (a,uu____65)::[] ->
                  let uu____82 = ua a in
                  FStar_Util.bind_opt uu____82
                    (fun a1  ->
                       let uu____88 = let uu____89 = f a1 in em uu____89 in
                       FStar_Pervasives_Native.Some uu____88)
              | uu____90 -> FStar_Pervasives_Native.None
let int2:
  'a 'b 'c .
    FStar_Ident.lid ->
      ('a -> 'b -> 'c) ->
        (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
          (FStar_Syntax_Syntax.term -> 'b FStar_Pervasives_Native.option) ->
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
                | (a,uu____178)::(b,uu____180)::[] ->
                    let uu____207 = ua a in
                    FStar_Util.bind_opt uu____207
                      (fun a1  ->
                         let uu____213 = ub b in
                         FStar_Util.bind_opt uu____213
                           (fun b1  ->
                              let uu____219 =
                                let uu____220 = f a1 b1 in em uu____220 in
                              FStar_Pervasives_Native.Some uu____219))
                | uu____221 -> FStar_Pervasives_Native.None
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
  let uu____363 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view in
  let uu____364 =
    let uu____367 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        FStar_Reflection_Basic.embed_term in
    let uu____368 =
      let uu____371 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          FStar_Syntax_Embeddings.embed_string_list in
      let uu____374 =
        let uu____377 =
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv
            (FStar_Syntax_Embeddings.unembed_list
               FStar_Syntax_Embeddings.unembed_string)
            FStar_Reflection_Basic.embed_fvar in
        let uu____380 =
          let uu____383 =
            mk11 "__inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Basic.unembed_comp
              FStar_Reflection_Basic.embed_comp_view in
          let uu____384 =
            let uu____387 =
              mk11 "__pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Basic.unembed_comp_view
                FStar_Reflection_Basic.embed_comp in
            let uu____388 =
              let uu____391 =
                mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Syntax_Embeddings.embed_string in
              let uu____392 =
                let uu____395 =
                  mk2 "__compare_binder"
                    FStar_Reflection_Basic.compare_binder
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.embed_order in
                let uu____396 =
                  let uu____399 =
                    mk11 "__type_of_binder"
                      FStar_Reflection_Basic.type_of_binder
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_term in
                  let uu____406 =
                    let uu____409 =
                      mk2 "__is_free" FStar_Reflection_Basic.is_free
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Reflection_Basic.unembed_term
                        FStar_Syntax_Embeddings.embed_bool in
                    let uu____410 =
                      let uu____413 =
                        mk11 "__fresh_binder"
                          FStar_Reflection_Basic.fresh_binder
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_binder in
                      let uu____420 =
                        let uu____423 =
                          mk2 "__term_eq" FStar_Reflection_Basic.term_eq
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.unembed_term
                            FStar_Syntax_Embeddings.embed_bool in
                        let uu____424 =
                          let uu____427 =
                            mk11 "__term_to_string"
                              FStar_Reflection_Basic.term_to_string
                              FStar_Reflection_Basic.unembed_term
                              FStar_Syntax_Embeddings.embed_string in
                          let uu____428 =
                            let uu____431 =
                              mk11 "__binders_of_env"
                                FStar_Reflection_Basic.binders_of_env
                                FStar_Reflection_Basic.unembed_env
                                FStar_Reflection_Basic.embed_binders in
                            let uu____432 =
                              let uu____435 =
                                mk2 "__lookup_typ"
                                  FStar_Reflection_Basic.lookup_typ
                                  FStar_Reflection_Basic.unembed_env
                                  FStar_Syntax_Embeddings.unembed_string_list
                                  FStar_Reflection_Basic.embed_sigelt_view in
                              [uu____435] in
                            uu____431 :: uu____432 in
                          uu____427 :: uu____428 in
                        uu____423 :: uu____424 in
                      uu____413 :: uu____420 in
                    uu____409 :: uu____410 in
                  uu____399 :: uu____406 in
                uu____395 :: uu____396 in
              uu____391 :: uu____392 in
            uu____387 :: uu____388 in
          uu____383 :: uu____384 in
        uu____377 :: uu____380 in
      uu____371 :: uu____374 in
    uu____367 :: uu____368 in
  uu____363 :: uu____364