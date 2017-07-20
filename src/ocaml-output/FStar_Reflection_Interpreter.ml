open Prims
let int1 :
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
                    let uu____79 = let uu____80 = ua a  in f uu____80  in
                    em uu____79  in
                  FStar_Pervasives_Native.Some uu____78
              | uu____81 -> FStar_Pervasives_Native.None
  
let int2 :
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
                        let uu____192 = ua a  in
                        let uu____193 = ub b  in f uu____192 uu____193  in
                      em uu____191  in
                    FStar_Pervasives_Native.Some uu____190
                | uu____194 -> FStar_Pervasives_Native.None
  
let reflection_primops :
  FStar_TypeChecker_Normalize.primitive_step Prims.list =
  let mklid nm = FStar_Reflection_Data.fstar_refl_syntax_lid nm  in
  let mk1 l arity fn =
    {
      FStar_TypeChecker_Normalize.name = l;
      FStar_TypeChecker_Normalize.arity = arity;
      FStar_TypeChecker_Normalize.strong_reduction_ok = false;
      FStar_TypeChecker_Normalize.interpretation = fn
    }  in
  let mk11 nm f u1 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "1") (int1 l f u1 em)  in
  let mk2 nm f u1 u2 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em)  in
  let uu____324 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view
     in
  let uu____325 =
    let uu____328 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        FStar_Reflection_Basic.embed_term
       in
    let uu____329 =
      let uu____332 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          FStar_Reflection_Basic.embed_string_list
         in
      let uu____335 =
        let uu____338 =
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv
            (FStar_Reflection_Basic.unembed_list
               FStar_Reflection_Basic.unembed_string)
            FStar_Reflection_Basic.embed_fvar
           in
        let uu____341 =
          let uu____344 =
            mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
              FStar_Reflection_Basic.unembed_binder
              FStar_Reflection_Basic.embed_string
             in
          let uu____345 =
            let uu____348 =
              mk2 "__compare_binder" FStar_Reflection_Basic.order_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.embed_order
               in
            let uu____349 =
              let uu____352 =
                mk11 "__type_of_binder"
                  (fun uu____362  ->
                     match uu____362 with
                     | (b,q) -> b.FStar_Syntax_Syntax.sort)
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Reflection_Basic.embed_term
                 in
              let uu____371 =
                let uu____374 =
                  mk2 "__is_free" FStar_Reflection_Basic.is_free
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_bool
                   in
                let uu____375 =
                  let uu____378 =
                    mk11 "__fresh_binder"
                      (fun t  ->
                         let uu____388 =
                           FStar_Syntax_Syntax.gen_bv "__refl"
                             FStar_Pervasives_Native.None t
                            in
                         (uu____388, FStar_Pervasives_Native.None))
                      FStar_Reflection_Basic.unembed_term
                      FStar_Reflection_Basic.embed_binder
                     in
                  let uu____391 =
                    let uu____394 =
                      mk2 "__term_eq" FStar_Syntax_Util.term_eq
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.embed_bool
                       in
                    let uu____399 =
                      let uu____402 =
                        mk11 "__term_to_string"
                          FStar_Syntax_Print.term_to_string
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_string
                         in
                      let uu____403 =
                        let uu____406 =
                          mk11 "__binders_of_env"
                            FStar_TypeChecker_Env.all_binders
                            FStar_Reflection_Basic.unembed_env
                            FStar_Reflection_Basic.embed_binders
                           in
                        let uu____407 =
                          let uu____410 =
                            mk2 "__lookup_typ"
                              FStar_Reflection_Basic.lookup_typ
                              FStar_Reflection_Basic.unembed_env
                              FStar_Reflection_Basic.unembed_string_list
                              FStar_Reflection_Basic.embed_sigelt_view
                             in
                          [uu____410]  in
                        uu____406 :: uu____407  in
                      uu____402 :: uu____403  in
                    uu____394 :: uu____399  in
                  uu____378 :: uu____391  in
                uu____374 :: uu____375  in
              uu____352 :: uu____371  in
            uu____348 :: uu____349  in
          uu____344 :: uu____345  in
        uu____338 :: uu____341  in
      uu____332 :: uu____335  in
    uu____328 :: uu____329  in
  uu____324 :: uu____325 