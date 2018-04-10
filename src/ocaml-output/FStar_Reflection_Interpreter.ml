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
             let uu____257 = FStar_TypeChecker_Normalize.psc_range ctxt  in
             fn uu____257 args)
    }  in
  let mk11 a b nm f u1 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "1") (int1 l f u1 em)  in
  let mk2 a b c nm f u1 u2 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em)  in
  let uu____353 =
    mk11 () () "inspect_ln"
      (fun a246  -> (Obj.magic FStar_Reflection_Basic.inspect_ln) a246)
      (Obj.magic FStar_Reflection_Embeddings.e_term)
      (Obj.magic FStar_Reflection_Embeddings.e_term_view)
     in
  let uu____354 =
    let uu____357 =
      mk11 () () "pack_ln"
        (fun a247  -> (Obj.magic FStar_Reflection_Basic.pack_ln) a247)
        (Obj.magic FStar_Reflection_Embeddings.e_term_view)
        (Obj.magic FStar_Reflection_Embeddings.e_term)
       in
    let uu____358 =
      let uu____361 =
        mk11 () () "inspect_fv"
          (fun a248  -> (Obj.magic FStar_Reflection_Basic.inspect_fv) a248)
          (Obj.magic FStar_Reflection_Embeddings.e_fv)
          (Obj.magic FStar_Syntax_Embeddings.e_string_list)
         in
      let uu____362 =
        let uu____365 =
          let uu____366 =
            FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
             in
          mk11 () () "pack_fv"
            (fun a249  -> (Obj.magic FStar_Reflection_Basic.pack_fv) a249)
            (Obj.magic uu____366)
            (Obj.magic FStar_Reflection_Embeddings.e_fv)
           in
        let uu____371 =
          let uu____374 =
            mk11 () () "inspect_comp"
              (fun a250  ->
                 (Obj.magic FStar_Reflection_Basic.inspect_comp) a250)
              (Obj.magic FStar_Reflection_Embeddings.e_comp)
              (Obj.magic FStar_Reflection_Embeddings.e_comp_view)
             in
          let uu____375 =
            let uu____378 =
              mk11 () () "pack_comp"
                (fun a251  ->
                   (Obj.magic FStar_Reflection_Basic.pack_comp) a251)
                (Obj.magic FStar_Reflection_Embeddings.e_comp_view)
                (Obj.magic FStar_Reflection_Embeddings.e_comp)
               in
            let uu____379 =
              let uu____382 =
                mk11 () () "inspect_sigelt"
                  (fun a252  ->
                     (Obj.magic FStar_Reflection_Basic.inspect_sigelt) a252)
                  (Obj.magic FStar_Reflection_Embeddings.e_sigelt)
                  (Obj.magic FStar_Reflection_Embeddings.e_sigelt_view)
                 in
              let uu____383 =
                let uu____386 =
                  mk11 () () "pack_sigelt"
                    (fun a253  ->
                       (Obj.magic FStar_Reflection_Basic.pack_sigelt) a253)
                    (Obj.magic FStar_Reflection_Embeddings.e_sigelt_view)
                    (Obj.magic FStar_Reflection_Embeddings.e_sigelt)
                   in
                let uu____387 =
                  let uu____390 =
                    mk11 () () "inspect_bv"
                      (fun a254  ->
                         (Obj.magic FStar_Reflection_Basic.inspect_bv) a254)
                      (Obj.magic FStar_Reflection_Embeddings.e_bv)
                      (Obj.magic FStar_Reflection_Embeddings.e_bv_view)
                     in
                  let uu____391 =
                    let uu____394 =
                      mk11 () () "pack_bv"
                        (fun a255  ->
                           (Obj.magic FStar_Reflection_Basic.pack_bv) a255)
                        (Obj.magic FStar_Reflection_Embeddings.e_bv_view)
                        (Obj.magic FStar_Reflection_Embeddings.e_bv)
                       in
                    let uu____395 =
                      let uu____398 =
                        mk11 () () "inspect_binder"
                          (fun a256  ->
                             (Obj.magic FStar_Reflection_Basic.inspect_binder)
                               a256)
                          (Obj.magic FStar_Reflection_Embeddings.e_binder)
                          (Obj.magic
                             FStar_Reflection_Embeddings.e_binder_view)
                         in
                      let uu____399 =
                        let uu____402 =
                          mk2 () () () "pack_binder"
                            (fun a257  ->
                               fun a258  ->
                                 (Obj.magic
                                    FStar_Reflection_Basic.pack_binder) a257
                                   a258)
                            (Obj.magic FStar_Reflection_Embeddings.e_bv)
                            (Obj.magic FStar_Reflection_Embeddings.e_aqualv)
                            (Obj.magic FStar_Reflection_Embeddings.e_binder)
                           in
                        let uu____403 =
                          let uu____406 =
                            mk2 () () () "compare_bv"
                              (fun a259  ->
                                 fun a260  ->
                                   (Obj.magic
                                      FStar_Reflection_Basic.compare_bv) a259
                                     a260)
                              (Obj.magic FStar_Reflection_Embeddings.e_bv)
                              (Obj.magic FStar_Reflection_Embeddings.e_bv)
                              (Obj.magic FStar_Reflection_Embeddings.e_order)
                             in
                          let uu____407 =
                            let uu____410 =
                              mk2 () () () "is_free"
                                (fun a261  ->
                                   fun a262  ->
                                     (Obj.magic
                                        FStar_Reflection_Basic.is_free) a261
                                       a262)
                                (Obj.magic FStar_Reflection_Embeddings.e_bv)
                                (Obj.magic FStar_Reflection_Embeddings.e_term)
                                (Obj.magic FStar_Syntax_Embeddings.e_bool)
                               in
                            let uu____411 =
                              let uu____414 =
                                mk2 () () () "term_eq"
                                  (fun a263  ->
                                     fun a264  ->
                                       (Obj.magic
                                          FStar_Reflection_Basic.term_eq)
                                         a263 a264)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.e_term)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.e_term)
                                  (Obj.magic FStar_Syntax_Embeddings.e_bool)
                                 in
                              let uu____415 =
                                let uu____418 =
                                  let uu____419 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Syntax_Embeddings.e_string
                                     in
                                  mk11 () () "moduleof"
                                    (fun a265  ->
                                       (Obj.magic
                                          FStar_Reflection_Basic.moduleof)
                                         a265)
                                    (Obj.magic
                                       FStar_Reflection_Embeddings.e_env)
                                    (Obj.magic uu____419)
                                   in
                                let uu____424 =
                                  let uu____427 =
                                    mk11 () () "term_to_string"
                                      (fun a266  ->
                                         (Obj.magic
                                            FStar_Reflection_Basic.term_to_string)
                                           a266)
                                      (Obj.magic
                                         FStar_Reflection_Embeddings.e_term)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.e_string)
                                     in
                                  let uu____428 =
                                    let uu____431 =
                                      mk11 () () "binders_of_env"
                                        (fun a267  ->
                                           (Obj.magic
                                              FStar_Reflection_Basic.binders_of_env)
                                             a267)
                                        (Obj.magic
                                           FStar_Reflection_Embeddings.e_env)
                                        (Obj.magic
                                           FStar_Reflection_Embeddings.e_binders)
                                       in
                                    let uu____432 =
                                      let uu____435 =
                                        let uu____436 =
                                          FStar_Syntax_Embeddings.e_option
                                            FStar_Reflection_Embeddings.e_sigelt
                                           in
                                        mk2 () () () "lookup_typ"
                                          (fun a268  ->
                                             fun a269  ->
                                               (Obj.magic
                                                  FStar_Reflection_Basic.lookup_typ)
                                                 a268 a269)
                                          (Obj.magic
                                             FStar_Reflection_Embeddings.e_env)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.e_string_list)
                                          (Obj.magic uu____436)
                                         in
                                      [uu____435]  in
                                    uu____431 :: uu____432  in
                                  uu____427 :: uu____428  in
                                uu____418 :: uu____424  in
                              uu____414 :: uu____415  in
                            uu____410 :: uu____411  in
                          uu____406 :: uu____407  in
                        uu____402 :: uu____403  in
                      uu____398 :: uu____399  in
                    uu____394 :: uu____395  in
                  uu____390 :: uu____391  in
                uu____386 :: uu____387  in
              uu____382 :: uu____383  in
            uu____378 :: uu____379  in
          uu____374 :: uu____375  in
        uu____365 :: uu____371  in
      uu____361 :: uu____362  in
    uu____357 :: uu____358  in
  uu____353 :: uu____354 