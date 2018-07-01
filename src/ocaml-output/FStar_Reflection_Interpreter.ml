open Prims
let unembed :
  'Auu____9 .
    'Auu____9 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____9 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____35 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____35 true norm_cb
  
let try_unembed :
  'Auu____56 .
    'Auu____56 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____56 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____82 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____82 false norm_cb
  
let embed :
  'Auu____105 .
    'Auu____105 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____105 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea  ->
    fun r  ->
      fun x  ->
        fun norm_cb  ->
          let uu____134 = FStar_Syntax_Embeddings.embed ea x  in
          uu____134 r FStar_Pervasives_Native.None norm_cb
  
let int1 :
  'a 'r .
    FStar_Ident.lid ->
      ('a -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_Range.range ->
              FStar_Syntax_Embeddings.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun er  ->
          fun r  ->
            fun n1  ->
              fun args  ->
                match args with
                | (a,uu____243)::[] ->
                    let uu____268 = try_unembed ea a n1  in
                    FStar_Util.bind_opt uu____268
                      (fun a1  ->
                         let uu____276 =
                           let uu____277 = f a1  in embed er r uu____277 n1
                            in
                         FStar_Pervasives_Native.Some uu____276)
                | uu____280 -> FStar_Pervasives_Native.None
  
let int2 :
  'a 'b 'r .
    FStar_Ident.lid ->
      ('a -> 'b -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_Range.range ->
                FStar_Syntax_Embeddings.norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            fun r  ->
              fun n1  ->
                fun args  ->
                  match args with
                  | (a,uu____375)::(b,uu____377)::[] ->
                      let uu____418 = try_unembed ea a n1  in
                      FStar_Util.bind_opt uu____418
                        (fun a1  ->
                           let uu____426 = try_unembed eb b n1  in
                           FStar_Util.bind_opt uu____426
                             (fun b1  ->
                                let uu____434 =
                                  let uu____435 = f a1 b1  in
                                  embed er r uu____435 n1  in
                                FStar_Pervasives_Native.Some uu____434))
                  | uu____438 -> FStar_Pervasives_Native.None
  
let (reflection_primops : FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  let mklid nm = FStar_Reflection_Data.fstar_refl_basic_lid nm  in
  let mk1 l arity fn =
    let uu____486 =
      let uu____493 = FStar_Ident.lid_of_str "_"  in
      FStar_TypeChecker_NBETerm.dummy_interp uu____493  in
    {
      FStar_TypeChecker_Cfg.name = l;
      FStar_TypeChecker_Cfg.arity = arity;
      FStar_TypeChecker_Cfg.univ_arity = (Prims.parse_int "0");
      FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.None;
      FStar_TypeChecker_Cfg.strong_reduction_ok = false;
      FStar_TypeChecker_Cfg.requires_binder_substitution = false;
      FStar_TypeChecker_Cfg.interpretation =
        (fun ctxt  ->
           fun n1  ->
             fun args  ->
               let uu____503 = FStar_TypeChecker_Cfg.psc_range ctxt  in
               fn uu____503 n1 args);
      FStar_TypeChecker_Cfg.interpretation_nbe = uu____486
    }  in
  let mk11 nm f u1 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "1") (int1 l f u1 em)  in
  let mk2 nm f u1 u2 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em)  in
  let uu____623 =
    mk11 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
     in
  let uu____624 =
    let uu____627 =
      mk11 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term
       in
    let uu____628 =
      let uu____631 =
        mk11 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
         in
      let uu____634 =
        let uu____637 =
          let uu____638 =
            FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
             in
          mk11 "pack_fv" FStar_Reflection_Basic.pack_fv uu____638
            FStar_Reflection_Embeddings.e_fv
           in
        let uu____645 =
          let uu____648 =
            mk11 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
             in
          let uu____649 =
            let uu____652 =
              mk11 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
               in
            let uu____653 =
              let uu____656 =
                mk11 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                 in
              let uu____657 =
                let uu____660 =
                  mk11 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                   in
                let uu____661 =
                  let uu____664 =
                    mk11 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                     in
                  let uu____665 =
                    let uu____668 =
                      mk11 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                       in
                    let uu____669 =
                      let uu____672 =
                        mk11 "sigelt_attrs"
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_Embeddings.e_sigelt
                          FStar_Reflection_Embeddings.e_attributes
                         in
                      let uu____675 =
                        let uu____678 =
                          mk2 "set_sigelt_attrs"
                            FStar_Reflection_Basic.set_sigelt_attrs
                            FStar_Reflection_Embeddings.e_attributes
                            FStar_Reflection_Embeddings.e_sigelt
                            FStar_Reflection_Embeddings.e_sigelt
                           in
                        let uu____681 =
                          let uu____684 =
                            mk11 "inspect_binder"
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder_view
                             in
                          let uu____685 =
                            let uu____688 =
                              mk2 "pack_binder"
                                FStar_Reflection_Basic.pack_binder
                                FStar_Reflection_Embeddings.e_bv
                                FStar_Reflection_Embeddings.e_aqualv
                                FStar_Reflection_Embeddings.e_binder
                               in
                            let uu____689 =
                              let uu____692 =
                                mk2 "compare_bv"
                                  FStar_Reflection_Basic.compare_bv
                                  FStar_Reflection_Embeddings.e_bv
                                  FStar_Reflection_Embeddings.e_bv
                                  FStar_Reflection_Embeddings.e_order
                                 in
                              let uu____693 =
                                let uu____696 =
                                  mk2 "is_free"
                                    FStar_Reflection_Basic.is_free
                                    FStar_Reflection_Embeddings.e_bv
                                    FStar_Reflection_Embeddings.e_term
                                    FStar_Syntax_Embeddings.e_bool
                                   in
                                let uu____697 =
                                  let uu____700 =
                                    let uu____701 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Reflection_Embeddings.e_fv
                                       in
                                    mk2 "lookup_attr"
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_Embeddings.e_term
                                      FStar_Reflection_Embeddings.e_env
                                      uu____701
                                     in
                                  let uu____708 =
                                    let uu____711 =
                                      mk2 "term_eq"
                                        FStar_Reflection_Basic.term_eq
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Syntax_Embeddings.e_bool
                                       in
                                    let uu____712 =
                                      let uu____715 =
                                        let uu____716 =
                                          FStar_Syntax_Embeddings.e_list
                                            FStar_Syntax_Embeddings.e_string
                                           in
                                        mk11 "moduleof"
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_Embeddings.e_env
                                          uu____716
                                         in
                                      let uu____723 =
                                        let uu____726 =
                                          mk11 "term_to_string"
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_string
                                           in
                                        let uu____727 =
                                          let uu____730 =
                                            mk11 "binders_of_env"
                                              FStar_Reflection_Basic.binders_of_env
                                              FStar_Reflection_Embeddings.e_env
                                              FStar_Reflection_Embeddings.e_binders
                                             in
                                          let uu____731 =
                                            let uu____734 =
                                              let uu____735 =
                                                FStar_Syntax_Embeddings.e_option
                                                  FStar_Reflection_Embeddings.e_sigelt
                                                 in
                                              mk2 "lookup_typ"
                                                FStar_Reflection_Basic.lookup_typ
                                                FStar_Reflection_Embeddings.e_env
                                                FStar_Syntax_Embeddings.e_string_list
                                                uu____735
                                               in
                                            [uu____734]  in
                                          uu____730 :: uu____731  in
                                        uu____726 :: uu____727  in
                                      uu____715 :: uu____723  in
                                    uu____711 :: uu____712  in
                                  uu____700 :: uu____708  in
                                uu____696 :: uu____697  in
                              uu____692 :: uu____693  in
                            uu____688 :: uu____689  in
                          uu____684 :: uu____685  in
                        uu____678 :: uu____681  in
                      uu____672 :: uu____675  in
                    uu____668 :: uu____669  in
                  uu____664 :: uu____665  in
                uu____660 :: uu____661  in
              uu____656 :: uu____657  in
            uu____652 :: uu____653  in
          uu____648 :: uu____649  in
        uu____637 :: uu____645  in
      uu____631 :: uu____634  in
    uu____627 :: uu____628  in
  uu____623 :: uu____624 