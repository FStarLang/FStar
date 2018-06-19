open Prims
let int1 :
  'a 'r .
    FStar_Ident.lid ->
      ('a -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_Range.range ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun er  ->
          fun r  ->
            fun args  ->
              match args with
              | (a,uu____65)::[] ->
                  let uu____82 = FStar_Syntax_Embeddings.unembed ea a  in
                  FStar_Util.bind_opt uu____82
                    (fun a1  ->
                       let uu____88 =
                         let uu____89 = f a1  in
                         FStar_Syntax_Embeddings.embed er r uu____89  in
                       FStar_Pervasives_Native.Some uu____88)
              | uu____90 -> FStar_Pervasives_Native.None
  
let int2 :
  'a 'b 'r .
    FStar_Ident.lid ->
      ('a -> 'b -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_Range.range ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            fun r  ->
              fun args  ->
                match args with
                | (a,uu____174)::(b,uu____176)::[] ->
                    let uu____203 = FStar_Syntax_Embeddings.unembed ea a  in
                    FStar_Util.bind_opt uu____203
                      (fun a1  ->
                         let uu____209 = FStar_Syntax_Embeddings.unembed eb b
                            in
                         FStar_Util.bind_opt uu____209
                           (fun b1  ->
                              let uu____215 =
                                let uu____216 = f a1 b1  in
                                FStar_Syntax_Embeddings.embed er r uu____216
                                 in
                              FStar_Pervasives_Native.Some uu____215))
                | uu____217 -> FStar_Pervasives_Native.None
  
let (reflection_primops :
  FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  let mklid nm = FStar_Reflection_Data.fstar_refl_basic_lid nm  in
  let mk1 l arity fn =
    {
      FStar_TypeChecker_Normalize.name = l;
      FStar_TypeChecker_Normalize.arity = arity;
      FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.None;
      FStar_TypeChecker_Normalize.strong_reduction_ok = false;
      FStar_TypeChecker_Normalize.requires_binder_substitution = false;
      FStar_TypeChecker_Normalize.interpretation =
        (fun ctxt  ->
           fun args  ->
             let uu____261 = FStar_TypeChecker_Normalize.psc_range ctxt  in
             fn uu____261 args)
    }  in
  let mk11 nm f u1 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "1") (int1 l f u1 em)  in
  let mk2 nm f u1 u2 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em)  in
  let uu____379 =
    mk11 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
     in
  let uu____380 =
    let uu____383 =
      mk11 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term
       in
    let uu____384 =
      let uu____387 =
        mk11 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
         in
      let uu____390 =
        let uu____393 =
          let uu____394 =
            FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
             in
          mk11 "pack_fv" FStar_Reflection_Basic.pack_fv uu____394
            FStar_Reflection_Embeddings.e_fv
           in
        let uu____401 =
          let uu____404 =
            mk11 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
             in
          let uu____405 =
            let uu____408 =
              mk11 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
               in
            let uu____409 =
              let uu____412 =
                mk11 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                 in
              let uu____413 =
                let uu____416 =
                  mk11 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                   in
                let uu____417 =
                  let uu____420 =
                    mk11 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                     in
                  let uu____421 =
                    let uu____424 =
                      mk11 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                       in
                    let uu____425 =
                      let uu____428 =
                        mk11 "inspect_binder"
                          FStar_Reflection_Basic.inspect_binder
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Reflection_Embeddings.e_binder_view
                         in
                      let uu____429 =
                        let uu____432 =
                          mk2 "pack_binder"
                            FStar_Reflection_Basic.pack_binder
                            FStar_Reflection_Embeddings.e_bv
                            FStar_Reflection_Embeddings.e_aqualv
                            FStar_Reflection_Embeddings.e_binder
                           in
                        let uu____433 =
                          let uu____436 =
                            mk2 "compare_bv"
                              FStar_Reflection_Basic.compare_bv
                              FStar_Reflection_Embeddings.e_bv
                              FStar_Reflection_Embeddings.e_bv
                              FStar_Reflection_Embeddings.e_order
                             in
                          let uu____437 =
                            let uu____440 =
                              mk2 "is_free" FStar_Reflection_Basic.is_free
                                FStar_Reflection_Embeddings.e_bv
                                FStar_Reflection_Embeddings.e_term
                                FStar_Syntax_Embeddings.e_bool
                               in
                            let uu____441 =
                              let uu____444 =
                                let uu____445 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Reflection_Embeddings.e_fv
                                   in
                                mk2 "lookup_attr"
                                  FStar_Reflection_Basic.lookup_attr
                                  FStar_Reflection_Embeddings.e_term
                                  FStar_Reflection_Embeddings.e_env uu____445
                                 in
                              let uu____452 =
                                let uu____455 =
                                  mk2 "term_eq"
                                    FStar_Reflection_Basic.term_eq
                                    FStar_Reflection_Embeddings.e_term
                                    FStar_Reflection_Embeddings.e_term
                                    FStar_Syntax_Embeddings.e_bool
                                   in
                                let uu____456 =
                                  let uu____459 =
                                    let uu____460 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Syntax_Embeddings.e_string
                                       in
                                    mk11 "moduleof"
                                      FStar_Reflection_Basic.moduleof
                                      FStar_Reflection_Embeddings.e_env
                                      uu____460
                                     in
                                  let uu____467 =
                                    let uu____470 =
                                      mk11 "term_to_string"
                                        FStar_Reflection_Basic.term_to_string
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Syntax_Embeddings.e_string
                                       in
                                    let uu____471 =
                                      let uu____474 =
                                        mk11 "binders_of_env"
                                          FStar_Reflection_Basic.binders_of_env
                                          FStar_Reflection_Embeddings.e_env
                                          FStar_Reflection_Embeddings.e_binders
                                         in
                                      let uu____475 =
                                        let uu____478 =
                                          let uu____479 =
                                            FStar_Syntax_Embeddings.e_option
                                              FStar_Reflection_Embeddings.e_sigelt
                                             in
                                          mk2 "lookup_typ"
                                            FStar_Reflection_Basic.lookup_typ
                                            FStar_Reflection_Embeddings.e_env
                                            FStar_Syntax_Embeddings.e_string_list
                                            uu____479
                                           in
                                        [uu____478]  in
                                      uu____474 :: uu____475  in
                                    uu____470 :: uu____471  in
                                  uu____459 :: uu____467  in
                                uu____455 :: uu____456  in
                              uu____444 :: uu____452  in
                            uu____440 :: uu____441  in
                          uu____436 :: uu____437  in
                        uu____432 :: uu____433  in
                      uu____428 :: uu____429  in
                    uu____424 :: uu____425  in
                  uu____420 :: uu____421  in
                uu____416 :: uu____417  in
              uu____412 :: uu____413  in
            uu____408 :: uu____409  in
          uu____404 :: uu____405  in
        uu____393 :: uu____401  in
      uu____387 :: uu____390  in
    uu____383 :: uu____384  in
  uu____379 :: uu____380 