open Prims
let unembed :
  'Auu____65876 .
    'Auu____65876 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____65876 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____65902 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____65902 true norm_cb
  
let try_unembed :
  'Auu____65925 .
    'Auu____65925 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'Auu____65925 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____65951 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____65951 false norm_cb
  
let embed :
  'Auu____65976 .
    'Auu____65976 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'Auu____65976 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea  ->
    fun r  ->
      fun x  ->
        fun norm_cb  ->
          let uu____66005 = FStar_Syntax_Embeddings.embed ea x  in
          uu____66005 r FStar_Pervasives_Native.None norm_cb
  
let int1 :
  'a 'r .
    FStar_Ident.lid ->
      ('a -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            FStar_TypeChecker_Cfg.psc ->
              FStar_Syntax_Embeddings.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun er  ->
          fun psc  ->
            fun n1  ->
              fun args  ->
                match args with
                | (a,uu____66115)::[] ->
                    let uu____66140 = try_unembed ea a n1  in
                    FStar_Util.bind_opt uu____66140
                      (fun a1  ->
                         let uu____66148 =
                           let uu____66149 =
                             FStar_TypeChecker_Cfg.psc_range psc  in
                           let uu____66150 = f a1  in
                           embed er uu____66149 uu____66150 n1  in
                         FStar_Pervasives_Native.Some uu____66148)
                | uu____66153 -> FStar_Pervasives_Native.None
  
let int2 :
  'a 'b 'r .
    FStar_Ident.lid ->
      ('a -> 'b -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              FStar_TypeChecker_Cfg.psc ->
                FStar_Syntax_Embeddings.norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            fun psc  ->
              fun n1  ->
                fun args  ->
                  match args with
                  | (a,uu____66249)::(b,uu____66251)::[] ->
                      let uu____66292 = try_unembed ea a n1  in
                      FStar_Util.bind_opt uu____66292
                        (fun a1  ->
                           let uu____66300 = try_unembed eb b n1  in
                           FStar_Util.bind_opt uu____66300
                             (fun b1  ->
                                let uu____66308 =
                                  let uu____66309 =
                                    FStar_TypeChecker_Cfg.psc_range psc  in
                                  let uu____66310 = f a1 b1  in
                                  embed er uu____66309 uu____66310 n1  in
                                FStar_Pervasives_Native.Some uu____66308))
                  | uu____66313 -> FStar_Pervasives_Native.None
  
let nbe_int1 :
  'a 'r .
    FStar_Ident.lid ->
      ('a -> 'r) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.nbe_cbs ->
              FStar_TypeChecker_NBETerm.args ->
                FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun er  ->
          fun cb  ->
            fun args  ->
              match args with
              | (a,uu____66379)::[] ->
                  let uu____66388 = FStar_TypeChecker_NBETerm.unembed ea cb a
                     in
                  FStar_Util.bind_opt uu____66388
                    (fun a1  ->
                       let uu____66394 =
                         let uu____66395 = f a1  in
                         FStar_TypeChecker_NBETerm.embed er cb uu____66395
                          in
                       FStar_Pervasives_Native.Some uu____66394)
              | uu____66396 -> FStar_Pervasives_Native.None
  
let nbe_int2 :
  'a 'b 'r .
    FStar_Ident.lid ->
      ('a -> 'b -> 'r) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'b FStar_TypeChecker_NBETerm.embedding ->
            'r FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.nbe_cbs ->
                FStar_TypeChecker_NBETerm.args ->
                  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun m  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            fun cb  ->
              fun args  ->
                match args with
                | (a,uu____66481)::(b,uu____66483)::[] ->
                    let uu____66496 =
                      FStar_TypeChecker_NBETerm.unembed ea cb a  in
                    FStar_Util.bind_opt uu____66496
                      (fun a1  ->
                         let uu____66502 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b  in
                         FStar_Util.bind_opt uu____66502
                           (fun b1  ->
                              let uu____66508 =
                                let uu____66509 = f a1 b1  in
                                FStar_TypeChecker_NBETerm.embed er cb
                                  uu____66509
                                 in
                              FStar_Pervasives_Native.Some uu____66508))
                | uu____66510 -> FStar_Pervasives_Native.None
  
let (mklid : Prims.string -> FStar_Ident.lid) =
  fun nm  -> FStar_Reflection_Data.fstar_refl_basic_lid nm 
let (mk :
  FStar_Ident.lid ->
    Prims.int ->
      (FStar_TypeChecker_Cfg.psc ->
         FStar_Syntax_Embeddings.norm_cb ->
           FStar_Syntax_Syntax.args ->
             FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_NBETerm.nbe_cbs ->
           FStar_TypeChecker_NBETerm.args ->
             FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
          -> FStar_TypeChecker_Cfg.primitive_step)
  =
  fun l  ->
    fun arity  ->
      fun fn  ->
        fun nbe_fn  ->
          {
            FStar_TypeChecker_Cfg.name = l;
            FStar_TypeChecker_Cfg.arity = arity;
            FStar_TypeChecker_Cfg.univ_arity = (Prims.parse_int "0");
            FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.None;
            FStar_TypeChecker_Cfg.strong_reduction_ok = true;
            FStar_TypeChecker_Cfg.requires_binder_substitution = false;
            FStar_TypeChecker_Cfg.interpretation = fn;
            FStar_TypeChecker_Cfg.interpretation_nbe = nbe_fn
          }
  
let mk1 :
  'a 'na 'nr 'r .
    Prims.string ->
      ('a -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'r FStar_Syntax_Embeddings.embedding ->
            ('na -> 'nr) ->
              'na FStar_TypeChecker_NBETerm.embedding ->
                'nr FStar_TypeChecker_NBETerm.embedding ->
                  FStar_TypeChecker_Cfg.primitive_step
  =
  fun nm  ->
    fun f  ->
      fun ea  ->
        fun er  ->
          fun nf  ->
            fun ena  ->
              fun enr  ->
                let l = mklid nm  in
                mk l (Prims.parse_int "1") (int1 l f ea er)
                  (nbe_int1 l nf ena enr)
  
let mk2 :
  'a 'b 'na 'nb 'nr 'r .
    Prims.string ->
      ('a -> 'b -> 'r) ->
        'a FStar_Syntax_Embeddings.embedding ->
          'b FStar_Syntax_Embeddings.embedding ->
            'r FStar_Syntax_Embeddings.embedding ->
              ('na -> 'nb -> 'nr) ->
                'na FStar_TypeChecker_NBETerm.embedding ->
                  'nb FStar_TypeChecker_NBETerm.embedding ->
                    'nr FStar_TypeChecker_NBETerm.embedding ->
                      FStar_TypeChecker_Cfg.primitive_step
  =
  fun nm  ->
    fun f  ->
      fun ea  ->
        fun eb  ->
          fun er  ->
            fun nf  ->
              fun ena  ->
                fun enb  ->
                  fun enr  ->
                    let l = mklid nm  in
                    mk l (Prims.parse_int "2") (int2 l f ea eb er)
                      (nbe_int2 l nf ena enb enr)
  
let (reflection_primops : FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  let uu____66808 =
    mk1 "inspect_ln" FStar_Reflection_Basic.inspect_ln
      FStar_Reflection_Embeddings.e_term
      FStar_Reflection_Embeddings.e_term_view
      FStar_Reflection_Basic.inspect_ln FStar_Reflection_NBEEmbeddings.e_term
      FStar_Reflection_NBEEmbeddings.e_term_view
     in
  let uu____66810 =
    let uu____66813 =
      mk1 "pack_ln" FStar_Reflection_Basic.pack_ln
        FStar_Reflection_Embeddings.e_term_view
        FStar_Reflection_Embeddings.e_term FStar_Reflection_Basic.pack_ln
        FStar_Reflection_NBEEmbeddings.e_term_view
        FStar_Reflection_NBEEmbeddings.e_term
       in
    let uu____66815 =
      let uu____66818 =
        mk1 "inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Embeddings.e_fv
          FStar_Syntax_Embeddings.e_string_list
          FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_NBEEmbeddings.e_fv
          FStar_TypeChecker_NBETerm.e_string_list
         in
      let uu____66826 =
        let uu____66829 =
          mk1 "pack_fv" FStar_Reflection_Basic.pack_fv
            FStar_Syntax_Embeddings.e_string_list
            FStar_Reflection_Embeddings.e_fv FStar_Reflection_Basic.pack_fv
            FStar_TypeChecker_NBETerm.e_string_list
            FStar_Reflection_NBEEmbeddings.e_fv
           in
        let uu____66837 =
          let uu____66840 =
            mk1 "inspect_comp" FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_Embeddings.e_comp
              FStar_Reflection_Embeddings.e_comp_view
              FStar_Reflection_Basic.inspect_comp
              FStar_Reflection_NBEEmbeddings.e_comp
              FStar_Reflection_NBEEmbeddings.e_comp_view
             in
          let uu____66842 =
            let uu____66845 =
              mk1 "pack_comp" FStar_Reflection_Basic.pack_comp
                FStar_Reflection_Embeddings.e_comp_view
                FStar_Reflection_Embeddings.e_comp
                FStar_Reflection_Basic.pack_comp
                FStar_Reflection_NBEEmbeddings.e_comp_view
                FStar_Reflection_NBEEmbeddings.e_comp
               in
            let uu____66847 =
              let uu____66850 =
                mk1 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_Embeddings.e_sigelt
                  FStar_Reflection_Embeddings.e_sigelt_view
                  FStar_Reflection_Basic.inspect_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt
                  FStar_Reflection_NBEEmbeddings.e_sigelt_view
                 in
              let uu____66852 =
                let uu____66855 =
                  mk1 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_Embeddings.e_sigelt_view
                    FStar_Reflection_Embeddings.e_sigelt
                    FStar_Reflection_Basic.pack_sigelt
                    FStar_Reflection_NBEEmbeddings.e_sigelt_view
                    FStar_Reflection_NBEEmbeddings.e_sigelt
                   in
                let uu____66857 =
                  let uu____66860 =
                    mk1 "inspect_bv" FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_Embeddings.e_bv
                      FStar_Reflection_Embeddings.e_bv_view
                      FStar_Reflection_Basic.inspect_bv
                      FStar_Reflection_NBEEmbeddings.e_bv
                      FStar_Reflection_NBEEmbeddings.e_bv_view
                     in
                  let uu____66862 =
                    let uu____66865 =
                      mk1 "pack_bv" FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_Embeddings.e_bv_view
                        FStar_Reflection_Embeddings.e_bv
                        FStar_Reflection_Basic.pack_bv
                        FStar_Reflection_NBEEmbeddings.e_bv_view
                        FStar_Reflection_NBEEmbeddings.e_bv
                       in
                    let uu____66867 =
                      let uu____66870 =
                        mk1 "sigelt_attrs"
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_Embeddings.e_sigelt
                          FStar_Reflection_Embeddings.e_attributes
                          FStar_Reflection_Basic.sigelt_attrs
                          FStar_Reflection_NBEEmbeddings.e_sigelt
                          FStar_Reflection_NBEEmbeddings.e_attributes
                         in
                      let uu____66876 =
                        let uu____66879 =
                          mk2 "set_sigelt_attrs"
                            FStar_Reflection_Basic.set_sigelt_attrs
                            FStar_Reflection_Embeddings.e_attributes
                            FStar_Reflection_Embeddings.e_sigelt
                            FStar_Reflection_Embeddings.e_sigelt
                            FStar_Reflection_Basic.set_sigelt_attrs
                            FStar_Reflection_NBEEmbeddings.e_attributes
                            FStar_Reflection_NBEEmbeddings.e_sigelt
                            FStar_Reflection_NBEEmbeddings.e_sigelt
                           in
                        let uu____66885 =
                          let uu____66888 =
                            mk1 "inspect_binder"
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder_view
                              FStar_Reflection_Basic.inspect_binder
                              FStar_Reflection_NBEEmbeddings.e_binder
                              FStar_Reflection_NBEEmbeddings.e_binder_view
                             in
                          let uu____66890 =
                            let uu____66893 =
                              mk2 "pack_binder"
                                FStar_Reflection_Basic.pack_binder
                                FStar_Reflection_Embeddings.e_bv
                                FStar_Reflection_Embeddings.e_aqualv
                                FStar_Reflection_Embeddings.e_binder
                                FStar_Reflection_Basic.pack_binder
                                FStar_Reflection_NBEEmbeddings.e_bv
                                FStar_Reflection_NBEEmbeddings.e_aqualv
                                FStar_Reflection_NBEEmbeddings.e_binder
                               in
                            let uu____66895 =
                              let uu____66898 =
                                mk2 "compare_bv"
                                  FStar_Reflection_Basic.compare_bv
                                  FStar_Reflection_Embeddings.e_bv
                                  FStar_Reflection_Embeddings.e_bv
                                  FStar_Reflection_Embeddings.e_order
                                  FStar_Reflection_Basic.compare_bv
                                  FStar_Reflection_NBEEmbeddings.e_bv
                                  FStar_Reflection_NBEEmbeddings.e_bv
                                  FStar_Reflection_NBEEmbeddings.e_order
                                 in
                              let uu____66900 =
                                let uu____66903 =
                                  mk2 "is_free"
                                    FStar_Reflection_Basic.is_free
                                    FStar_Reflection_Embeddings.e_bv
                                    FStar_Reflection_Embeddings.e_term
                                    FStar_Syntax_Embeddings.e_bool
                                    FStar_Reflection_Basic.is_free
                                    FStar_Reflection_NBEEmbeddings.e_bv
                                    FStar_Reflection_NBEEmbeddings.e_term
                                    FStar_TypeChecker_NBETerm.e_bool
                                   in
                                let uu____66907 =
                                  let uu____66910 =
                                    let uu____66911 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Reflection_Embeddings.e_fv
                                       in
                                    let uu____66916 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Reflection_NBEEmbeddings.e_fv
                                       in
                                    mk2 "lookup_attr"
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_Embeddings.e_term
                                      FStar_Reflection_Embeddings.e_env
                                      uu____66911
                                      FStar_Reflection_Basic.lookup_attr
                                      FStar_Reflection_NBEEmbeddings.e_term
                                      FStar_Reflection_NBEEmbeddings.e_env
                                      uu____66916
                                     in
                                  let uu____66926 =
                                    let uu____66929 =
                                      mk2 "term_eq"
                                        FStar_Reflection_Basic.term_eq
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Reflection_Embeddings.e_term
                                        FStar_Syntax_Embeddings.e_bool
                                        FStar_Reflection_Basic.term_eq
                                        FStar_Reflection_NBEEmbeddings.e_term
                                        FStar_Reflection_NBEEmbeddings.e_term
                                        FStar_TypeChecker_NBETerm.e_bool
                                       in
                                    let uu____66933 =
                                      let uu____66936 =
                                        mk1 "moduleof"
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_Embeddings.e_env
                                          FStar_Syntax_Embeddings.e_string_list
                                          FStar_Reflection_Basic.moduleof
                                          FStar_Reflection_NBEEmbeddings.e_env
                                          FStar_TypeChecker_NBETerm.e_string_list
                                         in
                                      let uu____66944 =
                                        let uu____66947 =
                                          mk1 "term_to_string"
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_string
                                            FStar_Reflection_Basic.term_to_string
                                            FStar_Reflection_NBEEmbeddings.e_term
                                            FStar_TypeChecker_NBETerm.e_string
                                           in
                                        let uu____66951 =
                                          let uu____66954 =
                                            mk1 "binders_of_env"
                                              FStar_Reflection_Basic.binders_of_env
                                              FStar_Reflection_Embeddings.e_env
                                              FStar_Reflection_Embeddings.e_binders
                                              FStar_Reflection_Basic.binders_of_env
                                              FStar_Reflection_NBEEmbeddings.e_env
                                              FStar_Reflection_NBEEmbeddings.e_binders
                                             in
                                          let uu____66956 =
                                            let uu____66959 =
                                              let uu____66960 =
                                                FStar_Syntax_Embeddings.e_option
                                                  FStar_Reflection_Embeddings.e_sigelt
                                                 in
                                              let uu____66965 =
                                                FStar_TypeChecker_NBETerm.e_option
                                                  FStar_Reflection_NBEEmbeddings.e_sigelt
                                                 in
                                              mk2 "lookup_typ"
                                                FStar_Reflection_Basic.lookup_typ
                                                FStar_Reflection_Embeddings.e_env
                                                FStar_Syntax_Embeddings.e_string_list
                                                uu____66960
                                                FStar_Reflection_Basic.lookup_typ
                                                FStar_Reflection_NBEEmbeddings.e_env
                                                FStar_TypeChecker_NBETerm.e_string_list
                                                uu____66965
                                               in
                                            [uu____66959]  in
                                          uu____66954 :: uu____66956  in
                                        uu____66947 :: uu____66951  in
                                      uu____66936 :: uu____66944  in
                                    uu____66929 :: uu____66933  in
                                  uu____66910 :: uu____66926  in
                                uu____66903 :: uu____66907  in
                              uu____66898 :: uu____66900  in
                            uu____66893 :: uu____66895  in
                          uu____66888 :: uu____66890  in
                        uu____66879 :: uu____66885  in
                      uu____66870 :: uu____66876  in
                    uu____66865 :: uu____66867  in
                  uu____66860 :: uu____66862  in
                uu____66855 :: uu____66857  in
              uu____66850 :: uu____66852  in
            uu____66845 :: uu____66847  in
          uu____66840 :: uu____66842  in
        uu____66829 :: uu____66837  in
      uu____66818 :: uu____66826  in
    uu____66813 :: uu____66815  in
  uu____66808 :: uu____66810 