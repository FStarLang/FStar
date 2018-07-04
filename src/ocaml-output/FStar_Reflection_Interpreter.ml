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
               let uu____495 = FStar_TypeChecker_Cfg.psc_range ctxt  in
               fn uu____495 n1 args);
      FStar_TypeChecker_Cfg.interpretation_nbe =
        (fun _cb  ->
           fun args  ->
             let uu____507 = FStar_Ident.lid_of_str "_"  in
             FStar_TypeChecker_NBETerm.dummy_interp uu____507 args)
    }  in
  let mk11 nm f u1 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "1") (int1 l f u1 em)  in
  let mk2 nm f u1 u2 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em)  in
  let uu____625 =
    mk11 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
     in
  let uu____626 =
    let uu____629 =
      mk11 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term
       in
    let uu____630 =
      let uu____633 =
        mk11 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
         in
      let uu____636 =
        let uu____639 =
          let uu____640 =
            FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
             in
          mk11 "pack_fv" FStar_Reflection_Basic.pack_fv uu____640
            FStar_Reflection_Embeddings.e_fv
           in
        let uu____647 =
          let uu____650 =
            mk11 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
             in
          let uu____651 =
            let uu____654 =
              mk11 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
               in
            let uu____655 =
              let uu____658 =
                mk11 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                 in
              let uu____659 =
                let uu____662 =
                  mk11 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                   in
                let uu____663 =
                  let uu____666 =
                    mk11 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                     in
                  let uu____667 =
                    let uu____670 =
                      mk11 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                       in
                    let uu____671 =
                      let uu____674 =
                        mk11 "sigelt_attrs"
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_Embeddings.e_sigelt
                          FStar_Reflection_Embeddings.e_attributes
                         in
                      let uu____677 =
                        let uu____680 =
                          mk2 "set_sigelt_attrs"
                            FStar_Reflection_Basic.set_sigelt_attrs
                            FStar_Reflection_Embeddings.e_attributes
                            FStar_Reflection_Embeddings.e_sigelt
                            FStar_Reflection_Embeddings.e_sigelt
                           in
                        let uu____683 =
                          let uu____686 =
                            mk11 "inspect_binder"
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder_view
                             in
                          let uu____687 =
                            let uu____690 =
                              mk2 "pack_binder"
                                FStar_Reflection_Basic.pack_binder
                                FStar_Reflection_Embeddings.e_bv
                                FStar_Reflection_Embeddings.e_aqualv
                                FStar_Reflection_Embeddings.e_binder
                               in
                            let uu____691 =
                              let uu____694 =
                                mk2 "compare_bv"
                                  FStar_Reflection_Basic.compare_bv
                                  FStar_Reflection_Embeddings.e_bv
                                  FStar_Reflection_Embeddings.e_bv
                                  FStar_Reflection_Embeddings.e_order
                                 in
                              let uu____695 =
                                let uu____698 =
                                  mk2 "is_free"
                                    FStar_Reflection_Basic.is_free
                                    FStar_Reflection_Embeddings.e_bv
                                    FStar_Reflection_Embeddings.e_term
                                    FStar_Syntax_Embeddings.e_bool
                                   in
                                let uu____699 =
                                  let uu____702 =
                                    let uu____703 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Reflection_Embeddings.e_fv
                                       in
                                    mk2 "lookup_attr"
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_Embeddings.e_term
                                      FStar_Reflection_Embeddings.e_env
                                      uu____703
                                     in
                                  let uu____710 =
                                    let uu____713 =
                                      mk2 "term_eq"
                                        FStar_Reflection_Basic.term_eq
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Syntax_Embeddings.e_bool
                                       in
                                    let uu____714 =
                                      let uu____717 =
                                        let uu____718 =
                                          FStar_Syntax_Embeddings.e_list
                                            FStar_Syntax_Embeddings.e_string
                                           in
                                        mk11 "moduleof"
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_Embeddings.e_env
                                          uu____718
                                         in
                                      let uu____725 =
                                        let uu____728 =
                                          mk11 "term_to_string"
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_string
                                           in
                                        let uu____729 =
                                          let uu____732 =
                                            mk11 "binders_of_env"
                                              FStar_Reflection_Basic.binders_of_env
                                              FStar_Reflection_Embeddings.e_env
                                              FStar_Reflection_Embeddings.e_binders
                                             in
                                          let uu____733 =
                                            let uu____736 =
                                              let uu____737 =
                                                FStar_Syntax_Embeddings.e_option
                                                  FStar_Reflection_Embeddings.e_sigelt
                                                 in
                                              mk2 "lookup_typ"
                                                FStar_Reflection_Basic.lookup_typ
                                                FStar_Reflection_Embeddings.e_env
                                                FStar_Syntax_Embeddings.e_string_list
                                                uu____737
                                               in
                                            [uu____736]  in
                                          uu____732 :: uu____733  in
                                        uu____728 :: uu____729  in
                                      uu____717 :: uu____725  in
                                    uu____713 :: uu____714  in
                                  uu____702 :: uu____710  in
                                uu____698 :: uu____699  in
                              uu____694 :: uu____695  in
                            uu____690 :: uu____691  in
                          uu____686 :: uu____687  in
                        uu____680 :: uu____683  in
                      uu____674 :: uu____677  in
                    uu____670 :: uu____671  in
                  uu____666 :: uu____667  in
                uu____662 :: uu____663  in
              uu____658 :: uu____659  in
            uu____654 :: uu____655  in
          uu____650 :: uu____651  in
        uu____639 :: uu____647  in
      uu____633 :: uu____636  in
    uu____629 :: uu____630  in
  uu____625 :: uu____626 