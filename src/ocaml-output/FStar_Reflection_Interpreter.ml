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
      FStar_TypeChecker_Normalize.requires_binder_substitution = false;
      FStar_TypeChecker_Normalize.interpretation =
        (fun ctxt  ->
           fun args  ->
             let uu____257 = FStar_TypeChecker_Normalize.psc_range ctxt in
             fn uu____257 args)
    } in
  let mk11 nm f u1 em =
    let l = mklid nm in mk1 l (Prims.parse_int "1") (int1 l f u1 em) in
  let mk2 nm f u1 u2 em =
    let l = mklid nm in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em) in
  let uu____369 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view in
  let uu____370 =
    let uu____373 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        FStar_Reflection_Basic.embed_term in
    let uu____374 =
      let uu____377 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          FStar_Syntax_Embeddings.embed_string_list in
      let uu____380 =
        let uu____383 =
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv
            (FStar_Syntax_Embeddings.unembed_list
               FStar_Syntax_Embeddings.unembed_string)
            FStar_Reflection_Basic.embed_fvar in
        let uu____386 =
          let uu____389 =
            mk11 "__inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Basic.unembed_comp
              FStar_Reflection_Basic.embed_comp_view in
          let uu____390 =
            let uu____393 =
              mk11 "__pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Basic.unembed_comp_view
                FStar_Reflection_Basic.embed_comp in
            let uu____394 =
              let uu____397 =
                mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Syntax_Embeddings.embed_string in
              let uu____398 =
                let uu____401 =
                  mk2 "__compare_binder"
                    FStar_Reflection_Basic.compare_binder
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.embed_order in
                let uu____402 =
                  let uu____405 =
                    mk11 "__type_of_binder"
                      FStar_Reflection_Basic.type_of_binder
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_term in
                  let uu____412 =
                    let uu____415 =
                      mk2 "__is_free" FStar_Reflection_Basic.is_free
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Reflection_Basic.unembed_term
                        FStar_Syntax_Embeddings.embed_bool in
                    let uu____416 =
                      let uu____419 =
                        mk11 "__fresh_binder"
                          FStar_Reflection_Basic.fresh_binder
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_binder in
                      let uu____426 =
                        let uu____429 =
                          mk2 "__term_eq" FStar_Reflection_Basic.term_eq
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.unembed_term
                            FStar_Syntax_Embeddings.embed_bool in
                        let uu____430 =
                          let uu____433 =
                            mk11 "__term_to_string"
                              FStar_Reflection_Basic.term_to_string
                              FStar_Reflection_Basic.unembed_term
                              FStar_Syntax_Embeddings.embed_string in
                          let uu____434 =
                            let uu____437 =
                              mk11 "__binders_of_env"
                                FStar_Reflection_Basic.binders_of_env
                                FStar_Reflection_Basic.unembed_env
                                FStar_Reflection_Basic.embed_binders in
                            let uu____438 =
                              let uu____441 =
                                mk2 "__lookup_typ"
                                  FStar_Reflection_Basic.lookup_typ
                                  FStar_Reflection_Basic.unembed_env
                                  FStar_Syntax_Embeddings.unembed_string_list
                                  FStar_Reflection_Basic.embed_sigelt_view in
                              [uu____441] in
                            uu____437 :: uu____438 in
                          uu____433 :: uu____434 in
                        uu____429 :: uu____430 in
                      uu____419 :: uu____426 in
                    uu____415 :: uu____416 in
                  uu____405 :: uu____412 in
                uu____401 :: uu____402 in
              uu____397 :: uu____398 in
            uu____393 :: uu____394 in
          uu____389 :: uu____390 in
        uu____383 :: uu____386 in
      uu____377 :: uu____380 in
    uu____373 :: uu____374 in
  uu____369 :: uu____370