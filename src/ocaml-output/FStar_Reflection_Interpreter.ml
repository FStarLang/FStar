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
              | (a,uu____51)::[] ->
                  let uu____68 = FStar_Syntax_Embeddings.unembed ea a  in
                  FStar_Util.bind_opt uu____68
                    (fun a1  ->
                       let uu____74 =
                         let uu____75 = f a1  in
                         FStar_Syntax_Embeddings.embed er r uu____75  in
                       FStar_Pervasives_Native.Some uu____74)
              | uu____76 -> FStar_Pervasives_Native.None
  
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
                | (a,uu____143)::(b,uu____145)::[] ->
                    let uu____172 = FStar_Syntax_Embeddings.unembed ea a  in
                    FStar_Util.bind_opt uu____172
                      (fun a1  ->
                         let uu____178 = FStar_Syntax_Embeddings.unembed eb b
                            in
                         FStar_Util.bind_opt uu____178
                           (fun b1  ->
                              let uu____184 =
                                let uu____185 = f a1 b1  in
                                FStar_Syntax_Embeddings.embed er r uu____185
                                 in
                              FStar_Pervasives_Native.Some uu____184))
                | uu____186 -> FStar_Pervasives_Native.None
  
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
             let uu____222 = FStar_TypeChecker_Normalize.psc_range ctxt  in
             fn uu____222 args)
    }  in
  let mk11 a b nm f u1 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "1") (int1 l f u1 em)  in
  let mk2 a b c nm f u1 u2 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em)  in
  let uu____304 =
    mk11 () () "inspect_ln"
      (fun a393  -> (Obj.magic FStar_Reflection_Basic.inspect_ln) a393)
      (Obj.magic FStar_Reflection_Embeddings.e_term)
      (Obj.magic FStar_Reflection_Embeddings.e_term_view)
     in
  let uu____305 =
    let uu____308 =
      mk11 () () "pack_ln"
        (fun a394  -> (Obj.magic FStar_Reflection_Basic.pack_ln) a394)
        (Obj.magic FStar_Reflection_Embeddings.e_term_view)
        (Obj.magic FStar_Reflection_Embeddings.e_term)
       in
    let uu____309 =
      let uu____312 =
        mk11 () () "inspect_fv"
          (fun a395  -> (Obj.magic FStar_Reflection_Basic.inspect_fv) a395)
          (Obj.magic FStar_Reflection_Embeddings.e_fv)
          (Obj.magic FStar_Syntax_Embeddings.e_string_list)
         in
      let uu____313 =
        let uu____316 =
          let uu____317 =
            FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
             in
          mk11 () () "pack_fv"
            (fun a396  -> (Obj.magic FStar_Reflection_Basic.pack_fv) a396)
            (Obj.magic uu____317)
            (Obj.magic FStar_Reflection_Embeddings.e_fv)
           in
        let uu____322 =
          let uu____325 =
            mk11 () () "inspect_comp"
              (fun a397  ->
                 (Obj.magic FStar_Reflection_Basic.inspect_comp) a397)
              (Obj.magic FStar_Reflection_Embeddings.e_comp)
              (Obj.magic FStar_Reflection_Embeddings.e_comp_view)
             in
          let uu____326 =
            let uu____329 =
              mk11 () () "pack_comp"
                (fun a398  ->
                   (Obj.magic FStar_Reflection_Basic.pack_comp) a398)
                (Obj.magic FStar_Reflection_Embeddings.e_comp_view)
                (Obj.magic FStar_Reflection_Embeddings.e_comp)
               in
            let uu____330 =
              let uu____333 =
                mk11 () () "inspect_sigelt"
                  (fun a399  ->
                     (Obj.magic FStar_Reflection_Basic.inspect_sigelt) a399)
                  (Obj.magic FStar_Reflection_Embeddings.e_sigelt)
                  (Obj.magic FStar_Reflection_Embeddings.e_sigelt_view)
                 in
              let uu____334 =
                let uu____337 =
                  mk11 () () "pack_sigelt"
                    (fun a400  ->
                       (Obj.magic FStar_Reflection_Basic.pack_sigelt) a400)
                    (Obj.magic FStar_Reflection_Embeddings.e_sigelt_view)
                    (Obj.magic FStar_Reflection_Embeddings.e_sigelt)
                   in
                let uu____338 =
                  let uu____341 =
                    mk11 () () "inspect_bv"
                      (fun a401  ->
                         (Obj.magic FStar_Reflection_Basic.inspect_bv) a401)
                      (Obj.magic FStar_Reflection_Embeddings.e_bv)
                      (Obj.magic FStar_Reflection_Embeddings.e_bv_view)
                     in
                  let uu____342 =
                    let uu____345 =
                      mk11 () () "pack_bv"
                        (fun a402  ->
                           (Obj.magic FStar_Reflection_Basic.pack_bv) a402)
                        (Obj.magic FStar_Reflection_Embeddings.e_bv_view)
                        (Obj.magic FStar_Reflection_Embeddings.e_bv)
                       in
                    let uu____346 =
                      let uu____349 =
                        mk11 () () "inspect_binder"
                          (fun a403  ->
                             (Obj.magic FStar_Reflection_Basic.inspect_binder)
                               a403)
                          (Obj.magic FStar_Reflection_Embeddings.e_binder)
                          (Obj.magic
                             FStar_Reflection_Embeddings.e_binder_view)
                         in
                      let uu____350 =
                        let uu____353 =
                          mk2 () () () "pack_binder"
                            (fun a404  ->
                               fun a405  ->
                                 (Obj.magic
                                    FStar_Reflection_Basic.pack_binder) a404
                                   a405)
                            (Obj.magic FStar_Reflection_Embeddings.e_bv)
                            (Obj.magic FStar_Reflection_Embeddings.e_aqualv)
                            (Obj.magic FStar_Reflection_Embeddings.e_binder)
                           in
                        let uu____354 =
                          let uu____357 =
                            mk2 () () () "compare_bv"
                              (fun a406  ->
                                 fun a407  ->
                                   (Obj.magic
                                      FStar_Reflection_Basic.compare_bv) a406
                                     a407)
                              (Obj.magic FStar_Reflection_Embeddings.e_bv)
                              (Obj.magic FStar_Reflection_Embeddings.e_bv)
                              (Obj.magic FStar_Reflection_Embeddings.e_order)
                             in
                          let uu____358 =
                            let uu____361 =
                              mk2 () () () "is_free"
                                (fun a408  ->
                                   fun a409  ->
                                     (Obj.magic
                                        FStar_Reflection_Basic.is_free) a408
                                       a409)
                                (Obj.magic FStar_Reflection_Embeddings.e_bv)
                                (Obj.magic FStar_Reflection_Embeddings.e_term)
                                (Obj.magic FStar_Syntax_Embeddings.e_bool)
                               in
                            let uu____362 =
                              let uu____365 =
                                mk2 () () () "term_eq"
                                  (fun a410  ->
                                     fun a411  ->
                                       (Obj.magic
                                          FStar_Reflection_Basic.term_eq)
                                         a410 a411)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.e_term)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.e_term)
                                  (Obj.magic FStar_Syntax_Embeddings.e_bool)
                                 in
                              let uu____366 =
                                let uu____369 =
                                  let uu____370 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Syntax_Embeddings.e_string
                                     in
                                  mk11 () () "moduleof"
                                    (fun a412  ->
                                       (Obj.magic
                                          FStar_Reflection_Basic.moduleof)
                                         a412)
                                    (Obj.magic
                                       FStar_Reflection_Embeddings.e_env)
                                    (Obj.magic uu____370)
                                   in
                                let uu____375 =
                                  let uu____378 =
                                    mk11 () () "term_to_string"
                                      (fun a413  ->
                                         (Obj.magic
                                            FStar_Reflection_Basic.term_to_string)
                                           a413)
                                      (Obj.magic
                                         FStar_Reflection_Embeddings.e_term)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.e_string)
                                     in
                                  let uu____379 =
                                    let uu____382 =
                                      mk11 () () "binders_of_env"
                                        (fun a414  ->
                                           (Obj.magic
                                              FStar_Reflection_Basic.binders_of_env)
                                             a414)
                                        (Obj.magic
                                           FStar_Reflection_Embeddings.e_env)
                                        (Obj.magic
                                           FStar_Reflection_Embeddings.e_binders)
                                       in
                                    let uu____383 =
                                      let uu____386 =
                                        let uu____387 =
                                          FStar_Syntax_Embeddings.e_option
                                            FStar_Reflection_Embeddings.e_sigelt
                                           in
                                        mk2 () () () "lookup_typ"
                                          (fun a415  ->
                                             fun a416  ->
                                               (Obj.magic
                                                  FStar_Reflection_Basic.lookup_typ)
                                                 a415 a416)
                                          (Obj.magic
                                             FStar_Reflection_Embeddings.e_env)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.e_string_list)
                                          (Obj.magic uu____387)
                                         in
                                      [uu____386]  in
                                    uu____382 :: uu____383  in
                                  uu____378 :: uu____379  in
                                uu____369 :: uu____375  in
                              uu____365 :: uu____366  in
                            uu____361 :: uu____362  in
                          uu____357 :: uu____358  in
                        uu____353 :: uu____354  in
                      uu____349 :: uu____350  in
                    uu____345 :: uu____346  in
                  uu____341 :: uu____342  in
                uu____337 :: uu____338  in
              uu____333 :: uu____334  in
            uu____329 :: uu____330  in
          uu____325 :: uu____326  in
        uu____316 :: uu____322  in
      uu____312 :: uu____313  in
    uu____308 :: uu____309  in
  uu____304 :: uu____305 