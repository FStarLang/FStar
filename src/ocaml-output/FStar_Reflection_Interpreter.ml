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
                  let uu____90 = FStar_Syntax_Embeddings.try_unembed ea a  in
                  FStar_Util.bind_opt uu____90
                    (fun a1  ->
                       let uu____96 =
                         let uu____97 = f a1  in
                         FStar_Syntax_Embeddings.embed er r uu____97  in
                       FStar_Pervasives_Native.Some uu____96)
              | uu____98 -> FStar_Pervasives_Native.None
  
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
                | (a,uu____182)::(b,uu____184)::[] ->
                    let uu____225 = FStar_Syntax_Embeddings.try_unembed ea a
                       in
                    FStar_Util.bind_opt uu____225
                      (fun a1  ->
                         let uu____231 =
                           FStar_Syntax_Embeddings.try_unembed eb b  in
                         FStar_Util.bind_opt uu____231
                           (fun b1  ->
                              let uu____237 =
                                let uu____238 = f a1 b1  in
                                FStar_Syntax_Embeddings.embed er r uu____238
                                 in
                              FStar_Pervasives_Native.Some uu____237))
                | uu____239 -> FStar_Pervasives_Native.None
  
let (reflection_primops : FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  let mklid nm = FStar_Reflection_Data.fstar_refl_basic_lid nm  in
  let mk1 l arity fn =
    {
      FStar_TypeChecker_Cfg.name = l;
      FStar_TypeChecker_Cfg.arity = arity;
      FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.None;
      FStar_TypeChecker_Cfg.strong_reduction_ok = false;
      FStar_TypeChecker_Cfg.requires_binder_substitution = false;
      FStar_TypeChecker_Cfg.interpretation =
        (fun ctxt  ->
           fun args  ->
             let uu____283 = FStar_TypeChecker_Cfg.psc_range ctxt  in
             fn uu____283 args)
    }  in
  let mk11 nm f u1 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "1") (int1 l f u1 em)  in
  let mk2 nm f u1 u2 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em)  in
  let uu____401 =
    mk11 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
     in
  let uu____402 =
    let uu____405 =
      mk11 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term
       in
    let uu____406 =
      let uu____409 =
        mk11 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
         in
      let uu____412 =
        let uu____415 =
          let uu____416 =
            FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
             in
          mk11 "pack_fv" FStar_Reflection_Basic.pack_fv uu____416
            FStar_Reflection_Embeddings.e_fv
           in
        let uu____423 =
          let uu____426 =
            mk11 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
             in
          let uu____427 =
            let uu____430 =
              mk11 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
               in
            let uu____431 =
              let uu____434 =
                mk11 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                 in
              let uu____435 =
                let uu____438 =
                  mk11 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                   in
                let uu____439 =
                  let uu____442 =
                    mk11 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                     in
                  let uu____443 =
                    let uu____446 =
                      mk11 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                       in
                    let uu____447 =
                      let uu____450 =
                        mk11 "sigelt_attrs"
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_Embeddings.e_sigelt
                          FStar_Reflection_Embeddings.e_attributes
                         in
                      let uu____453 =
                        let uu____456 =
                          mk2 "set_sigelt_attrs"
                            FStar_Reflection_Basic.set_sigelt_attrs
                            FStar_Reflection_Embeddings.e_attributes
                            FStar_Reflection_Embeddings.e_sigelt
                            FStar_Reflection_Embeddings.e_sigelt
                           in
                        let uu____459 =
                          let uu____462 =
                            mk11 "inspect_binder"
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder_view
                             in
                          let uu____463 =
                            let uu____466 =
                              mk2 "pack_binder"
                                FStar_Reflection_Basic.pack_binder
                                FStar_Reflection_Embeddings.e_bv
                                FStar_Reflection_Embeddings.e_aqualv
                                FStar_Reflection_Embeddings.e_binder
                               in
                            let uu____467 =
                              let uu____470 =
                                mk2 "compare_bv"
                                  FStar_Reflection_Basic.compare_bv
                                  FStar_Reflection_Embeddings.e_bv
                                  FStar_Reflection_Embeddings.e_bv
                                  FStar_Reflection_Embeddings.e_order
                                 in
                              let uu____471 =
                                let uu____474 =
                                  mk2 "is_free"
                                    FStar_Reflection_Basic.is_free
                                    FStar_Reflection_Embeddings.e_bv
                                    FStar_Reflection_Embeddings.e_term
                                    FStar_Syntax_Embeddings.e_bool
                                   in
                                let uu____475 =
                                  let uu____478 =
                                    let uu____479 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Reflection_Embeddings.e_fv
                                       in
                                    mk2 "lookup_attr"
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_Embeddings.e_term
                                      FStar_Reflection_Embeddings.e_env
                                      uu____479
                                     in
                                  let uu____486 =
                                    let uu____489 =
                                      mk2 "term_eq"
                                        FStar_Reflection_Basic.term_eq
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Syntax_Embeddings.e_bool
                                       in
                                    let uu____490 =
                                      let uu____493 =
                                        let uu____494 =
                                          FStar_Syntax_Embeddings.e_list
                                            FStar_Syntax_Embeddings.e_string
                                           in
                                        mk11 "moduleof"
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_Embeddings.e_env
                                          uu____494
                                         in
                                      let uu____501 =
                                        let uu____504 =
                                          mk11 "term_to_string"
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_string
                                           in
                                        let uu____505 =
                                          let uu____508 =
                                            mk11 "binders_of_env"
                                              FStar_Reflection_Basic.binders_of_env
                                              FStar_Reflection_Embeddings.e_env
                                              FStar_Reflection_Embeddings.e_binders
                                             in
                                          let uu____509 =
                                            let uu____512 =
                                              let uu____513 =
                                                FStar_Syntax_Embeddings.e_option
                                                  FStar_Reflection_Embeddings.e_sigelt
                                                 in
                                              mk2 "lookup_typ"
                                                FStar_Reflection_Basic.lookup_typ
                                                FStar_Reflection_Embeddings.e_env
                                                FStar_Syntax_Embeddings.e_string_list
                                                uu____513
                                               in
                                            [uu____512]  in
                                          uu____508 :: uu____509  in
                                        uu____504 :: uu____505  in
                                      uu____493 :: uu____501  in
                                    uu____489 :: uu____490  in
                                  uu____478 :: uu____486  in
                                uu____474 :: uu____475  in
                              uu____470 :: uu____471  in
                            uu____466 :: uu____467  in
                          uu____462 :: uu____463  in
                        uu____456 :: uu____459  in
                      uu____450 :: uu____453  in
                    uu____446 :: uu____447  in
                  uu____442 :: uu____443  in
                uu____438 :: uu____439  in
              uu____434 :: uu____435  in
            uu____430 :: uu____431  in
          uu____426 :: uu____427  in
        uu____415 :: uu____423  in
      uu____409 :: uu____412  in
    uu____405 :: uu____406  in
  uu____401 :: uu____402 