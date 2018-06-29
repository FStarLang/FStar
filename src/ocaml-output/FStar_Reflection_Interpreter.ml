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
  
let embed :
  'Auu____58 .
    'Auu____58 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____58 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea  ->
    fun r  ->
      fun x  ->
        fun norm_cb  ->
          let uu____87 = FStar_Syntax_Embeddings.embed ea x  in
          uu____87 r FStar_Pervasives_Native.None norm_cb
  
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
                | (a,uu____196)::[] ->
                    let uu____221 = unembed ea a n1  in
                    FStar_Util.bind_opt uu____221
                      (fun a1  ->
                         let uu____229 =
                           let uu____230 = f a1  in embed er r uu____230 n1
                            in
                         FStar_Pervasives_Native.Some uu____229)
                | uu____233 -> FStar_Pervasives_Native.None
  
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
                  | (a,uu____328)::(b,uu____330)::[] ->
                      let uu____371 = unembed ea a n1  in
                      FStar_Util.bind_opt uu____371
                        (fun a1  ->
                           let uu____379 = unembed eb b n1  in
                           FStar_Util.bind_opt uu____379
                             (fun b1  ->
                                let uu____387 =
                                  let uu____388 = f a1 b1  in
                                  embed er r uu____388 n1  in
                                FStar_Pervasives_Native.Some uu____387))
                  | uu____391 -> FStar_Pervasives_Native.None
  
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
           fun n1  ->
             fun args  ->
               let uu____448 = FStar_TypeChecker_Normalize.psc_range ctxt  in
               fn uu____448 n1 args)
    }  in
  let mk11 nm f u1 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "1") (int1 l f u1 em)  in
  let mk2 nm f u1 u2 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em)  in
  let uu____568 =
    mk11 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
     in
  let uu____569 =
    let uu____572 =
      mk11 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term
       in
    let uu____573 =
      let uu____576 =
        mk11 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
         in
      let uu____579 =
        let uu____582 =
          let uu____583 =
            FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
             in
          mk11 "pack_fv" FStar_Reflection_Basic.pack_fv uu____583
            FStar_Reflection_Embeddings.e_fv
           in
        let uu____590 =
          let uu____593 =
            mk11 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
             in
          let uu____594 =
            let uu____597 =
              mk11 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
               in
            let uu____598 =
              let uu____601 =
                mk11 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                 in
              let uu____602 =
                let uu____605 =
                  mk11 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                   in
                let uu____606 =
                  let uu____609 =
                    mk11 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                     in
                  let uu____610 =
                    let uu____613 =
                      mk11 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                       in
                    let uu____614 =
                      let uu____617 =
                        mk11 "inspect_binder"
                          FStar_Reflection_Basic.inspect_binder
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Reflection_Embeddings.e_binder_view
                         in
                      let uu____618 =
                        let uu____621 =
                          mk2 "pack_binder"
                            FStar_Reflection_Basic.pack_binder
                            FStar_Reflection_Embeddings.e_bv
                            FStar_Reflection_Embeddings.e_aqualv
                            FStar_Reflection_Embeddings.e_binder
                           in
                        let uu____622 =
                          let uu____625 =
                            mk2 "compare_bv"
                              FStar_Reflection_Basic.compare_bv
                              FStar_Reflection_Embeddings.e_bv
                              FStar_Reflection_Embeddings.e_bv
                              FStar_Reflection_Embeddings.e_order
                             in
                          let uu____626 =
                            let uu____629 =
                              mk2 "is_free" FStar_Reflection_Basic.is_free
                                FStar_Reflection_Embeddings.e_bv
                                FStar_Reflection_Embeddings.e_term
                                FStar_Syntax_Embeddings.e_bool
                               in
                            let uu____630 =
                              let uu____633 =
                                let uu____634 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Reflection_Embeddings.e_fv
                                   in
                                mk2 "lookup_attr"
                                  FStar_Reflection_Basic.lookup_attr
                                  FStar_Reflection_Embeddings.e_term
                                  FStar_Reflection_Embeddings.e_env uu____634
                                 in
                              let uu____641 =
                                let uu____644 =
                                  mk2 "term_eq"
                                    FStar_Reflection_Basic.term_eq
                                    FStar_Reflection_Embeddings.e_term
                                    FStar_Reflection_Embeddings.e_term
                                    FStar_Syntax_Embeddings.e_bool
                                   in
                                let uu____645 =
                                  let uu____648 =
                                    let uu____649 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Syntax_Embeddings.e_string
                                       in
                                    mk11 "moduleof"
                                      FStar_Reflection_Basic.moduleof
                                      FStar_Reflection_Embeddings.e_env
                                      uu____649
                                     in
                                  let uu____656 =
                                    let uu____659 =
                                      mk11 "term_to_string"
                                        FStar_Reflection_Basic.term_to_string
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Syntax_Embeddings.e_string
                                       in
                                    let uu____660 =
                                      let uu____663 =
                                        mk11 "binders_of_env"
                                          FStar_Reflection_Basic.binders_of_env
                                          FStar_Reflection_Embeddings.e_env
                                          FStar_Reflection_Embeddings.e_binders
                                         in
                                      let uu____664 =
                                        let uu____667 =
                                          let uu____668 =
                                            FStar_Syntax_Embeddings.e_option
                                              FStar_Reflection_Embeddings.e_sigelt
                                             in
                                          mk2 "lookup_typ"
                                            FStar_Reflection_Basic.lookup_typ
                                            FStar_Reflection_Embeddings.e_env
                                            FStar_Syntax_Embeddings.e_string_list
                                            uu____668
                                           in
                                        [uu____667]  in
                                      uu____663 :: uu____664  in
                                    uu____659 :: uu____660  in
                                  uu____648 :: uu____656  in
                                uu____644 :: uu____645  in
                              uu____633 :: uu____641  in
                            uu____629 :: uu____630  in
                          uu____625 :: uu____626  in
                        uu____621 :: uu____622  in
                      uu____617 :: uu____618  in
                    uu____613 :: uu____614  in
                  uu____609 :: uu____610  in
                uu____605 :: uu____606  in
              uu____601 :: uu____602  in
            uu____597 :: uu____598  in
          uu____593 :: uu____594  in
        uu____582 :: uu____590  in
      uu____576 :: uu____579  in
    uu____572 :: uu____573  in
  uu____568 :: uu____569 